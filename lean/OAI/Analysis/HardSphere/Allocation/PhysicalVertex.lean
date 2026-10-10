import Mathlib
import OAI.Analysis.HardSphere.Comparison.ParameterTarget
import OAI.Analysis.HardSphere.Allocation.CoarsePhysical
import OAI.Analysis.HardSphere.Allocation.PhysicalTargets

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma exposedPeriodPair_at {E : Type*} [MeasurableSpace E] {L : Length}
    (Q : Kernel E Point) [IsFiniteKernel Q] {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z y' z' : E→Point) (hy : Measurable y) (hz : Measurable z)
    (hy' : Measurable y') (hz' : Measurable z') (c : Point) (hc : projectPoint L c=0)
    (S T U : Set (E×C(Time,Point))) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀e f,(e,shiftPath c f)∈U ↔ (e,f)∈T)
    (A : E→Set Point) (hQ : ∀e,Q e=targetUniform (A e)) (e : E)
    (hA : MeasurableSet (A e)) (hAf : volume (A e)≠⊤) {a b : ℝ≥0∞}
    (ha : 0<a) (hb : 0<b) (hvol : a≤volume (A e))
    (hbound : ∀u∈A e,‖u-(fun j ↦ (y e j+z e j)/2)‖≤C)
    (hbound' : ∀u∈A e,‖u-(fun j ↦ ((y' e+c) j+(z' e+c) j)/2)‖≤C)
    (hfirst : ∀ᵐu ∂targetUniform (A e),b≤trialKernel t (y e) (z e) u (Prod.mk e ⁻¹' S))
    (hsecond : ∀ᵐu ∂targetUniform (A e),b≤trialKernel t (y' e+c) (z' e+c) u (Prod.mk e ⁻¹' U)) :
    let ρ := exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU
    let P := parameterIndividualReference t y z hy hz S hS
    let P' := parameterIndividualReference t y' z' hy' hz' T hT
    let G := b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)
    IsProbabilityMeasure (ρ e) ∧ IsProbabilityMeasure (P e) ∧ IsProbabilityMeasure (P' e) ∧
      (ρ e).fst≤G • P e ∧ (ρ e).snd≤G • P' e ∧
      (∀ᵐp ∂ρ e,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let Q₀ := Kernel.const Unit (Q e)
  let S₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' S)
  let T₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' T)
  let U₀ : Set (Unit×C(Time,Point)) := Prod.snd ⁻¹' (Prod.mk e ⁻¹' U)
  have hs : MeasurableSet S₀ := (hS.preimage measurable_prodMk_left).preimage measurable_snd
  have ht' : MeasurableSet T₀ := (hT.preimage measurable_prodMk_left).preimage measurable_snd
  have hu : MeasurableSet U₀ := (hU.preimage measurable_prodMk_left).preimage measurable_snd
  have htu : ∀q f,(q,shiftPath c f)∈U₀ ↔ (q,f)∈T₀ := fun _ f ↦ hTU e f
  have hq : ∀q : Unit,Q₀ q=targetUniform (A e) := fun _ ↦ hQ e
  obtain ⟨hp,hm,hn,hdom,hmid⟩ := exposedPeriodPair_physical Q₀ ht hC
    (fun _ ↦ y e) (fun _ ↦ z e) (fun _ ↦ y' e) (fun _ ↦ z' e)
    measurable_const measurable_const measurable_const measurable_const c hc
    S₀ T₀ U₀ hs ht' hu htu (fun _ ↦ A e) hq (fun _ ↦ hA) (fun _ ↦ hAf)
    ha hb (fun _ ↦ hvol) (fun _ ↦ hbound) (fun _ ↦ hbound')
    (fun _ ↦ hfirst) (fun _ ↦ hsecond)
  let ρ₀ := exposedPeriodPair Q₀ t (fun _ ↦ y e) (fun _ ↦ z e)
    (fun _ ↦ y' e) (fun _ ↦ z' e) measurable_const measurable_const
    measurable_const measurable_const c S₀ U₀ hs hu
  have he : ρ₀ ()=exposedPeriodPair Q t y z y' z' hy hz hy' hz' c S U hS hU e := by
    rw [exposedPeriodPair_apply Q t y z y' z' hy hz hy' hz' c S U hS hU A hQ e]
    exact exposedPeriodPair_apply Q₀ t _ _ _ _ _ _ _ _ c S₀ U₀ hs hu (fun _ ↦ A e) hq ()
  have hme : parameterIndividualReference t (fun _ : Unit ↦ y e) (fun _ ↦ z e)
      measurable_const measurable_const S₀ hs ()=parameterIndividualReference t y z hy hz S hS e := by
    rw [parameterIndividualReference_apply,parameterIndividualReference_apply]
    rfl
  have hne : parameterIndividualReference t (fun _ : Unit ↦ y' e) (fun _ ↦ z' e)
      measurable_const measurable_const T₀ ht' ()=parameterIndividualReference t y' z' hy' hz' T hT e := by
    rw [parameterIndividualReference_apply,parameterIndividualReference_apply]
    rfl
  have hf := hdom ()
  have hi := hmid ()
  change (ρ₀ ()).fst≤_ ∧ (ρ₀ ()).snd≤_ at hf
  change ∀ᵐp ∂ρ₀ (),_ at hi
  rw [he,hme,hne] at hf
  rw [he] at hi
  refine ⟨?_,?_,?_,hf.1,hf.2,hi⟩
  · rw [←he]; exact hp.isProbabilityMeasure ()
  · rw [←hme]; exact hm.isProbabilityMeasure ()
  · rw [←hne]; exact hn.isProbabilityMeasure ()

end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma datumAccessible_endpoints {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) (hi : datumAccessible hL g m t r R C S u i d) :
    ‖datumStart hL d i-anchorPoint (datumHome hL d i)‖≤10 ∧
    ‖datumEnd hL d i-anchorPoint (datumHome hL d i)‖≤10 := by
  have ha : 0<volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i 0) :=
    lt_of_lt_of_le (by norm_num) (hi 0)
  obtain ⟨U,hU⟩ := nonempty_of_measure_ne_zero ha.ne'
  have hs : 0<trialKernel t (datumStart hL d i) (datumEnd hL d i) U
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ)) hU.2
  obtain ⟨f,hf⟩ := nonempty_of_measure_ne_zero hs.ne'
  exact ⟨by rw [←hf.2.2.1.1]; exact (hf.2.1 0).1,
    by rw [←hf.2.2.1.2]; exact (hf.2.1 1).1⟩

lemma midpoint_bound (v y z U : Point) (hy : ‖y-v‖≤10) (hz : ‖z-v‖≤10)
    (hU : ‖U-v‖≤3) : ‖U-(fun j ↦ (y j+z j)/2)‖≤13 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤13)).mpr
  intro j
  have hyj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mp hy j
  have hzj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤10)).mp hz j
  have huj := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤3)).mp hU j
  change |y j-v j|≤10 at hyj
  change |z j-v j|≤10 at hzj
  change |U j-v j|≤3 at huj
  change |U j-(y j+z j)/2|≤13
  rw [abs_le] at hyj hzj huj ⊢
  constructor <;> linarith

lemma unitTarget_sub (v c U : Point) : U-c∈unitTarget v ↔ U∈unitTarget (v+c) := by
  simp only [unitTarget,mem_pi,mem_univ,forall_const,mem_Ico,Pi.sub_apply,Pi.add_apply]
  constructor <;> intro h j <;> specialize h j <;> constructor <;> linarith [h.1,h.2]

def routeCellPeriod {K : ℕ} (v w : Fin 3→Fin K) (j : Fin 7) : Point :=
  anchorPoint v-(anchorPoint w+targetStep j)

lemma routeCellPeriod_chart {K : ℕ} (v w : Fin 3→Fin K) (j : Fin 7) :
    anchorPoint w+targetStep j+routeCellPeriod v w j=anchorPoint v := by
  unfold routeCellPeriod
  abel

def vertexTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Set (PhysicalDatum N K M G L×Point) :=
  (univ×ˢunitTarget (anchorPoint v))∩
    (datumTarget hL g m t r R C S u i 0 ∩
      (fun p ↦ (p.1,p.2-routeCellPeriod v w j)) ⁻¹'
        datumTarget hL g m t r R C S u i' j)

lemma vertexTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    MeasurableSet (vertexTarget (M:=M) hL g m t r R C S u i i' v w j) :=
  (MeasurableSet.univ.prod (unitTarget_measurable _)).inter
    ((datumTarget_measurable hL g m t r R C S u i 0).inter
      ((datumTarget_measurable hL g m t r R C S u i' j).preimage
        (measurable_fst.prodMk (measurable_snd.sub measurable_const))))

lemma vertexTarget_subset {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L) :
    Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j ⊆ unitTarget (anchorPoint v) :=
  fun _ h ↦ h.1.2

lemma vertexTarget_volume {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L)
    (hv : datumHome hL d i=v) (hw : datumHome hL d i'=w)
    (hi : datumAccessible hL g m t r R C S u i d)
    (hi' : datumAccessible hL g m t r R C S u i' d) :
    ENNReal.ofReal (49/50:ℝ)≤volume
      (Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j) := by
  let B := unitTarget (anchorPoint v)
  let A := Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i 0
  let T := (fun U : Point ↦ U-routeCellPeriod v w j) ⁻¹'
    (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i' j)
  have hA : MeasurableSet A := (datumTarget_measurable hL g m t r R C S u i 0).preimage measurable_prodMk_left
  have hT : MeasurableSet T := ((datumTarget_measurable hL g m t r R C S u i' j).preimage
    measurable_prodMk_left).preimage (measurable_id.sub measurable_const)
  have hAB : A⊆B := by
    intro U hU
    have h := hU.1
    simpa [hv,targetStep,B] using h
  have hTB : T⊆B := by
    intro U hU
    have h := hU.1
    rw [hw,unitTarget_sub,routeCellPeriod_chart] at h
    exact h
  have htvol : volume T=volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i' j) := by
    exact (measurePreserving_add_right volume (-routeCellPeriod v w j)).measure_preimage
      ((datumTarget_measurable hL g m t r R C S u i' j).preimage measurable_prodMk_left).nullMeasurableSet
  let : IsProbabilityMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ,unitTarget_volume]⟩
  have ha : ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B) A := by
    rw [Measure.restrict_apply hA,inter_eq_left.mpr hAB]
    exact hi 0
  have ht : ENNReal.ofReal (99/100:ℝ)≤(volume.restrict B) T := by
    rw [Measure.restrict_apply hT,inter_eq_left.mpr hTB,htvol]
    exact hi' j
  have H := probability_inter_98 (volume.restrict B) hA hT ha ht
  rw [Measure.restrict_apply (hA.inter hT)] at H
  convert H using 1
  congr 1
  ext U
  simp only [vertexTarget,mem_preimage,mem_inter_iff,mem_prod,mem_univ,true_and,A,T,B]
  tauto

def shiftedDatumPermitted {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point) :
    Set (PhysicalDatum N K M G L×C(Time,Point)) :=
  (fun p ↦ (p.1,Bridge.shiftPath (-c) p.2)) ⁻¹' datumPermitted hL g m r R C S u i

lemma shiftedDatumPermitted_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point) :
    MeasurableSet (shiftedDatumPermitted (M:=M) hL g m r R C S u i c) :=
  (datumPermitted_measurable hL g m r R C S u i).preimage
    (measurable_fst.prodMk ((Bridge.shiftPath_continuous (-c)).measurable.comp measurable_snd))

lemma shiftedDatumPermitted_equiv {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time) (i : Fin N) (c : Point)
    (d : PhysicalDatum N K M G L) (f : C(Time,Point)) :
    (d,Bridge.shiftPath c f)∈shiftedDatumPermitted hL g m r R C S u i c ↔
      (d,f)∈datumPermitted hL g m r R C S u i := by
  simp only [shiftedDatumPermitted,mem_preimage,Bridge.shiftPath_cancel]

lemma datumSuccess_shift {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (c : Point)
    (d : PhysicalDatum N K M G L) (U : Point) :
    trialKernel t (datumStart hL d i+c) (datumEnd hL d i+c) U
      (Prod.mk d ⁻¹' shiftedDatumPermitted hL g m r R C S u i c)=
    datumSuccess hL g m t r R C S u i (d,U-c) := by
  have H := trialKernel_shift t (datumStart hL d i) (datumEnd hL d i) (U-c) c
  rw [sub_add_cancel] at H
  rw [←H,Measure.map_apply (Bridge.shiftPath_continuous c).measurable
    ((shiftedDatumPermitted_measurable hL g m r R C S u i c).preimage measurable_prodMk_left)]
  congr 1
  ext f
  exact shiftedDatumPermitted_equiv hL g m r R C S u i c d f

def vertexPair {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    Kernel (PhysicalDatum N K M G L) (C(Time,Point)×C(Time,Point)) :=
  exposedPeriodPair
    (parameterTargetKernel (B:=unitTarget (anchorPoint v)) (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
      (vertexTarget hL g m t r R C S u i i' v w j)
      (vertexTarget_measurable hL g m t r R C S u i i' v w j)) t
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (fun d ↦ datumStart hL d i') (fun d ↦ datumEnd hL d i')
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumStart_measurable hL i') (datumEnd_measurable hL i') (routeCellPeriod v w j)
    (datumPermitted hL g m r R C S u i)
    (shiftedDatumPermitted hL g m r R C S u i' (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (shiftedDatumPermitted_measurable hL g m r R C S u i' (routeCellPeriod v w j))

instance vertexPair_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    IsFiniteKernel (vertexPair (M:=M) hL g m t r R C S u i i' v w j) := by
  unfold vertexPair exposedPeriodPair exposedPairedTrialKernel parameterPairedKernel
  infer_instance

def vertexDensityBound (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (9/10:ℝ))⁻¹*((ENNReal.ofReal (49/50:ℝ))⁻¹*(midpointLower t 13)⁻¹)

theorem vertexPair_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i i' : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hv : datumHome hL d i=v) (hw : datumHome hL d i'=w)
    (hi : datumAccessible hL g m t r R C S u i d)
    (hi' : datumAccessible hL g m t r R C S u i' d) :
    let ρ := vertexPair hL g m t r R C S u i i' v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    let P' := datumIndividualReference hL g m r R C S t u i' d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
      ρ.fst≤vertexDensityBound t • P ∧ ρ.snd≤vertexDensityBound t • P' ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L (p.2 midpointTime)) := by
  dsimp only
  let A := fun d : PhysicalDatum N K M G L ↦
    Prod.mk d ⁻¹' vertexTarget hL g m t r R C S u i i' v w j
  have hA : MeasurableSet (A d) :=
    (vertexTarget_measurable hL g m t r R C S u i i' v w j).preimage measurable_prodMk_left
  have hAf : volume (A d)≠⊤ := ne_top_of_le_ne_top
    (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
    (measure_mono (vertexTarget_subset hL g m t r R C S u i i' v w j d))
  have hmem : ∀ᵐU ∂targetUniform (A d),U∈A d :=
    Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hei := datumAccessible_endpoints hL g m t r R C S u i d hi
  have hei' := datumAccessible_endpoints hL g m t r R C S u i' d hi'
  apply exposedPeriodPair_at _ ht (by norm_num : (0:ℝ)≤13)
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (fun d ↦ datumStart hL d i') (fun d ↦ datumEnd hL d i')
    (datumStart_measurable hL i) (datumEnd_measurable hL i)
    (datumStart_measurable hL i') (datumEnd_measurable hL i')
    (routeCellPeriod v w j) hc (datumPermitted hL g m r R C S u i)
    (datumPermitted hL g m r R C S u i')
    (shiftedDatumPermitted hL g m r R C S u i' (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (datumPermitted_measurable hL g m r R C S u i')
    (shiftedDatumPermitted_measurable hL g m r R C S u i' (routeCellPeriod v w j))
    (shiftedDatumPermitted_equiv hL g m r R C S u i' (routeCellPeriod v w j))
    A (parameterTargetKernel_apply _ _ _ (vertexTarget_subset hL g m t r R C S u i i' v w j)) d
    hA hAf (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (49/50:ℝ))
    (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ))
    (vertexTarget_volume hL g m t r R C S u i i' v w j d hv hw hi hi')
  · intro U hU
    exact midpoint_bound _ _ _ U hei.1 hei.2
      (targetCell_radius _ 0 U hU.2.1.1)
  · intro U hU
    have H := midpoint_bound _ _ _ (U-routeCellPeriod v w j) hei'.1 hei'.2
      (targetCell_radius _ j _ hU.2.2.1)
    convert H using 1
    congr 1
    ext k
    change U k-((datumStart hL d i' k+routeCellPeriod v w j k)+
      (datumEnd hL d i' k+routeCellPeriod v w j k))/2=
      (U k-routeCellPeriod v w j k)-(datumStart hL d i' k+datumEnd hL d i' k)/2
    ring
  · filter_upwards [hmem] with U hU
    exact hU.2.1.2
  · filter_upwards [hmem] with U hU
    rw [datumSuccess_shift]
    exact hU.2.2.2

end HardSphere.Groups
end
end

end OAI
