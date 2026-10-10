import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalVertex

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener Comparison GaussianPacking
variable {E : Type*} [MeasurableSpace E]

def exposedPeriodSingle (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    Kernel E (C(Time,Point)×Point) :=
  (Q ⊗ₖ parameterSuccessKernel
    (parameterTrialKernel t (fun e ↦ y e+c) (fun e ↦ z e+c)
      (hy.add measurable_const) (hz.add measurable_const))
    (exposedSuccess S) (exposedSuccess_measurable hS)).map
      (fun p ↦ (shiftPath (-c) p.2,p.1))

instance exposedPeriodSingle_finite (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) :
    IsFiniteKernel (exposedPeriodSingle Q t y z hy hz c S hS) := by
  unfold exposedPeriodSingle
  infer_instance

lemma exposedPeriodSingle_apply (Q : Kernel E Point) [IsFiniteKernel Q] (t : ℝ)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) :
    exposedPeriodSingle Q t y z hy hz c S hS e =
      ((Q e).compProd (successKernel (trialKernel t (y e+c) (z e+c))
        (Prod.mk e ⁻¹' S) (hS.preimage measurable_prodMk_left))).map
        (fun p ↦ (shiftPath (-c) p.2,p.1)) := by
  rw [exposedPeriodSingle,Kernel.map_apply _ (by fun_prop)]
  congr 1
  ext B hB
  rw [Kernel.compProd_apply hB,Measure.compProd_apply hB]
  apply lintegral_congr
  intro U
  rw [parameterTrialSuccess_apply]
  exact hS

lemma successJoint_fst (μ : Measure Point) [SFinite μ] (t : ℝ) (y z : Point)
    (S : Set C(Time,Point)) (hS : MeasurableSet S)
    (hp : ∀ᵐU ∂μ,0<trialKernel t y z U S) :
    (μ.compProd (successKernel (trialKernel t y z) S hS)).fst=μ := by
  ext B hB
  rw [Measure.fst_apply hB,Measure.compProd_apply (hB.preimage measurable_fst)]
  calc
    _ = ∫⁻U,B.indicator (fun _ ↦ (1:ℝ≥0∞)) U ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with U hU
      by_cases h : U∈B
      · simp only [Set.indicator_of_mem h]
        rw [show (fun x : C(Time,Point) ↦ (U,x)) ⁻¹' (Prod.fst ⁻¹' B)=univ by
          ext x; simp [h]]
        exact successKernel_mass _ S hS hU
      · rw [show (fun x : C(Time,Point) ↦ (U,x)) ⁻¹' (Prod.fst ⁻¹' B)=∅ by
          ext x; simp [h]]
        simp [h]
    _ = μ B := by rw [lintegral_indicator hB]; simp

lemma exposedPeriodSingle_physical {L : Length} (Q : Kernel E Point) [IsFiniteKernel Q]
    {t C : ℝ} (ht : 0<t) (hC : 0≤C)
    (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (c : Point)
    (hc : projectPoint L c=0) (S T : Set (E×C(Time,Point)))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hst : ∀e f,(e,shiftPath c f)∈T ↔ (e,f)∈S)
    (e : E) (A B : Set Point) (hQ : Q e=targetUniform A)
    (hA : MeasurableSet A) (hAf : volume A≠⊤) (hAB : A⊆B) (hBvol : volume B=1)
    {a b : ℝ≥0∞} (ha : 0<a) (hb : 0<b) (hvol : a≤volume A)
    (hbound : ∀U∈A,‖U-(fun k ↦ ((y e+c) k+(z e+c) k)/2)‖≤C)
    (hs : ∀ᵐU ∂targetUniform A,b≤trialKernel t (y e+c) (z e+c) U (Prod.mk e ⁻¹' T)) :
    let ρ := exposedPeriodSingle Q t y z hy hz c T hT e
    let P := parameterIndividualReference t y z hy hz S hS e
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      ρ.fst≤(b⁻¹*(a⁻¹*(midpointLower t C)⁻¹)) • P ∧
      ρ.snd≤a⁻¹ • targetUniform B ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L p.2) := by
  dsimp only
  have hA0 : volume A≠0 := (ha.trans_le hvol).ne'
  let := targetUniform_probability hA0 hAf
  let μ := (targetUniform A).compProd (successKernel (trialKernel t (y e+c) (z e+c))
    (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left))
  have hp : ∀ᵐU ∂targetUniform A,0<trialKernel t (y e+c) (z e+c) U (Prod.mk e ⁻¹' T) :=
    hs.mono fun _ h ↦ hb.trans_le h
  have hf : μ.fst=targetUniform A := successJoint_fst _ _ _ _ _ _ hp
  have hm : IsProbabilityMeasure μ := ⟨by
    have H := congrArg (fun ν : Measure Point ↦ ν univ) hf
    simpa only [Measure.fst_apply MeasurableSet.univ,preimage_univ,measure_univ] using H⟩
  let := hm
  have hmap : Measurable (fun p : Point×C(Time,Point) ↦ (shiftPath (-c) p.2,p.1)) := by fun_prop
  have hr : exposedPeriodSingle Q t y z hy hz c T hT e=
      μ.map (fun p ↦ (shiftPath (-c) p.2,p.1)) := by
    rw [exposedPeriodSingle_apply,hQ]
  have href := individualReference_unshift t (y e) (z e) c (Prod.mk e ⁻¹' S)
    (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) (hst e)
  have hP : IsProbabilityMeasure (parameterIndividualReference t y z hy hz S hS e) := by
    rw [parameterIndividualReference_apply,←href]
    let := individualReference_probability ht hC (y e+c) (z e+c) hA hA0 hAf hbound
      (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) hb hs
    infer_instance
  refine ⟨?_,hP,?_,?_,?_⟩
  · rw [hr]
    infer_instance
  · have HD := physical_trial_le_reference ht hC (y e+c) (z e+c) hA hAf hbound
      (Prod.mk e ⁻¹' T) (hT.preimage measurable_prodMk_left) hs
    have HD' := Measure.map_mono HD (shiftPath_continuous (-c)).measurable
    rw [Measure.map_smul _ (shiftPath_continuous (-c)).measurable.aemeasurable,href] at HD'
    rw [hr,Measure.fst,Measure.map_map measurable_fst hmap,parameterIndividualReference_apply]
    apply (show μ.map (fun p ↦ shiftPath (-c) p.2)≤
      (b⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • individualReference t (y e) (z e)
        (Prod.mk e ⁻¹' S) by
      convert HD' using 1
      rw [Measure.map_map (shiftPath_continuous (-c)).measurable measurable_snd]
      rfl).trans
    intro D
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) le_rfl)) le_rfl
  · rw [hr,Measure.snd,Measure.map_map measurable_snd hmap]
    change μ.fst≤_
    rw [hf]
    simp only [targetUniform,hBvol,inv_one,one_smul]
    intro D
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) (Measure.restrict_mono_set _ hAB D)
  · rw [hr]
    apply (ae_map_iff hmap.aemeasurable (by measurability)).mpr
    have HH : ∀ᵐp ∂μ,p.2 midpointTime=p.1 := by
      apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun
        ((continuous_eval_const midpointTime).measurable.comp measurable_snd) measurable_fst)
      apply ae_of_all
      intro U
      exact (successKernel_absolutelyContinuous _ _ _ U).ae_le (trialKernel_midpoint t (y e+c) (z e+c) U)
    filter_upwards [HH] with p hp
    have hc' : projectPoint L (-c)=0 := by
      ext j
      change (((-c j):ℝ):AddCircle L.val)=0
      rw [AddCircle.coe_neg]
      have h := congrFun hc j
      change ((c j:ℝ):AddCircle L.val)=0 at h
      rw [h,neg_zero]
    change projectPoint L (p.2 midpointTime+(-c))=projectPoint L p.1
    rw [projectPoint_shift (-c) hc',hp]

end HardSphere.Bridge

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def endpointTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Set (PhysicalDatum N K M G L×Point) :=
  (univ×ˢunitTarget (anchorPoint v)) ∩
    (fun p ↦ (p.1,p.2-routeCellPeriod v w j)) ⁻¹' datumTarget hL g m t r R C S u i j

lemma endpointTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    MeasurableSet (endpointTarget (M:=M) hL g m t r R C S u i v w j) :=
  (MeasurableSet.univ.prod (unitTarget_measurable _)).inter
    ((datumTarget_measurable hL g m t r R C S u i j).preimage (by fun_prop))

lemma endpointTarget_subset {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L) :
    Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j ⊆ unitTarget (anchorPoint v) :=
  fun _ h ↦ h.1.2

lemma endpointTarget_volume {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (d : PhysicalDatum N K M G L)
    (hw : datumHome hL d i=w) (hi : datumAccessible hL g m t r R C S u i d) :
    ENNReal.ofReal (49/50:ℝ)≤volume (Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j) := by
  have he : Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j=
      (fun U ↦ U-routeCellPeriod v w j) ⁻¹' (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j) := by
    ext U
    constructor
    · exact fun h ↦ h.2
    · intro h
      refine ⟨⟨mem_univ _,?_⟩,h⟩
      have H := h.1
      rw [hw,unitTarget_sub,routeCellPeriod_chart] at H
      exact H
  rw [he]
  have hvol : volume ((fun U ↦ U-routeCellPeriod v w j) ⁻¹'
      (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j))=
      volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j) :=
    (measurePreserving_add_right volume (-routeCellPeriod v w j)).measure_preimage
      ((datumTarget_measurable hL g m t r R C S u i j).preimage measurable_prodMk_left).nullMeasurableSet
  rw [hvol]
  exact (by norm_num : ENNReal.ofReal (49/50:ℝ)≤ENNReal.ofReal (99/100:ℝ)).trans (hi j)

def endpointPair {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) : Kernel (PhysicalDatum N K M G L) (C(Time,Point)×Point) :=
  exposedPeriodSingle
    (parameterTargetKernel (B:=unitTarget (anchorPoint v)) (by rw [unitTarget_volume]; exact ENNReal.one_ne_top)
      (endpointTarget hL g m t r R C S u i v w j)
      (endpointTarget_measurable hL g m t r R C S u i v w j)) t
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i) (routeCellPeriod v w j)
    (shiftedDatumPermitted hL g m r R C S u i (routeCellPeriod v w j))
    (shiftedDatumPermitted_measurable hL g m r R C S u i (routeCellPeriod v w j))

instance endpointPair_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) :
    IsFiniteKernel (endpointPair (M:=M) hL g m t r R C S u i v w j) := by
  unfold endpointPair
  infer_instance

theorem endpointPair_physical {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time) (i : Fin N)
    (v w : Fin 3→Fin K) (j : Fin 7) (hc : projectPoint L (routeCellPeriod v w j)=0)
    (d : PhysicalDatum N K M G L) (hw : datumHome hL d i=w)
    (hi : datumAccessible hL g m t r R C S u i d) :
    let ρ := endpointPair hL g m t r R C S u i v w j d
    let P := datumIndividualReference hL g m r R C S t u i d
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      ρ.fst≤vertexDensityBound t • P ∧
      ρ.snd≤(ENNReal.ofReal (49/50:ℝ))⁻¹ • targetUniform (unitTarget (anchorPoint v)) ∧
      (∀ᵐp ∂ρ,projectPoint L (p.1 midpointTime)=projectPoint L p.2) := by
  dsimp only
  let A := Prod.mk d ⁻¹' endpointTarget hL g m t r R C S u i v w j
  have hA : MeasurableSet A :=
    (endpointTarget_measurable hL g m t r R C S u i v w j).preimage measurable_prodMk_left
  have hAB := endpointTarget_subset hL g m t r R C S u i v w j d
  have hAf : volume A≠⊤ := ne_top_of_le_ne_top
    (by rw [unitTarget_volume]; exact ENNReal.one_ne_top) (measure_mono hAB)
  have hmem : ∀ᵐU ∂targetUniform A,U∈A := Measure.ae_smul_measure (ae_restrict_mem hA) _
  have hei := datumAccessible_endpoints hL g m t r R C S u i d hi
  apply exposedPeriodSingle_physical _ ht (by norm_num : (0:ℝ)≤13)
    (fun d ↦ datumStart hL d i) (fun d ↦ datumEnd hL d i)
    (datumStart_measurable hL i) (datumEnd_measurable hL i) (routeCellPeriod v w j) hc
    (datumPermitted hL g m r R C S u i)
    (shiftedDatumPermitted hL g m r R C S u i (routeCellPeriod v w j))
    (datumPermitted_measurable hL g m r R C S u i)
    (shiftedDatumPermitted_measurable hL g m r R C S u i (routeCellPeriod v w j))
    (shiftedDatumPermitted_equiv hL g m r R C S u i (routeCellPeriod v w j)) d
    A (unitTarget (anchorPoint v))
    (parameterTargetKernel_apply _ _ _ (endpointTarget_subset hL g m t r R C S u i v w j) d)
    hA hAf hAB (unitTarget_volume _) (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (49/50:ℝ))
    (by norm_num : (0:ℝ≥0∞)<ENNReal.ofReal (9/10:ℝ))
    (endpointTarget_volume hL g m t r R C S u i v w j d hw hi)
  · intro U hU
    have H := midpoint_bound _ _ _ (U-routeCellPeriod v w j) hei.1 hei.2
      (targetCell_radius _ j _ hU.2.1)
    convert H using 1
    congr 1
    ext k
    change U k-((datumStart hL d i k+routeCellPeriod v w j k)+
      (datumEnd hL d i k+routeCellPeriod v w j k))/2=
      (U k-routeCellPeriod v w j k)-(datumStart hL d i k+datumEnd hL d i k)/2
    ring
  · filter_upwards [hmem] with U hU
    rw [datumSuccess_shift]
    exact hU.2.2

end HardSphere.Groups
end
end

end OAI
