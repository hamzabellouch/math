import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReferenceResample
import OAI.Analysis.HardSphere.Allocation.PhysicalAssembly
import OAI.Analysis.HardSphere.Allocation.PhysicalDatum

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital

lemma nearestLift_eq_of_near {L : Length} (hL : 50<L.val) (c y : Point)
    (hy : ‖y-c‖≤3) : nearestLift L c (projectPoint L y)=y := by
  ext j
  have hj : |y j-c j|≤3 := (norm_le_pi_norm (y-c) j).trans hy
  have hmem : y j-c j∈Set.Ico (-L.val/2) (-L.val/2+L.val) := by
    rw [abs_le] at hj
    constructor <;> linarith
  change ((AddCircle.equivIco L.val (-L.val/2)) ((y j:AddCircle L.val)-(c j:AddCircle L.val))).val+c j=y j
  rw [←AddCircle.coe_sub,AddCircle.equivIco_coe_eq hmem]
  simp

lemma near_lift_unique {L : Length} (hL : 50<L.val) (c y : Point) (x : Torus L)
    (hp : projectPoint L y=x) (hy : ‖y-c‖≤3) : y=nearestLift L c x := by
  subst x
  exact (nearestLift_eq_of_near hL c y hy).symm

attribute [local instance] Classical.propDecidable

theorem canonical_certificate_useful_list {ell b Alo A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hAlo : 0 < Alo) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D α : ℝ,D₀ ≤ D → Alo ≤ α → α ≤ A →
    ∀(N K m n : ℕ) [Nontrivial (Fin N)] (L : Length),50 < L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀(w : Time),t*(w:ℝ)=D⁻¹ →
    ∀(θ : ℝ),θ ≤ ell/6 →
    ∀(v : Fin 3→Fin K) (c : Point),projectPoint L c=gridCenter L v →
    ∀(ω : ConfigurationPath N L),
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    ∀(label : Fin m→Fin N),Function.Injective label →
    Finset.univ.image label=eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω →
    ∀(B : Fin 7→Set Point),(∀j,MeasurableSet (B j)) → (∀j,volume (B j)=1) →
      (∀j u,u∈B j → ‖u-c‖ ≤ 3) →
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) w (nearestLift L c (ω 0 (label i))) (nearestLift L c (ω 1 (label i)))
      c (fun j ↦ onePathAt j ω) (label i) B)).card:ℝ) ≤ (m:ℝ)/10 := by
  obtain ⟨cG,MG,hcG,hMG,htail⟩ := wiener_norm_gaussian_tail
  have htail' (R : ℝ) (hR : 0 ≤ R) :
      wiener {β | R ≤ ‖β‖} ≤ ENNReal.ofReal MG.toReal*ENNReal.ofReal (Real.exp (-cG*R^2)) := by
    rw [ENNReal.ofReal_toReal hMG.ne]
    exact htail R hR
  obtain ⟨t₀,ht₀,hs⟩ := physical_useful_list hell hb hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₁,hD₁,hs⟩ := hs t ht htt (t/Alo^2+1) MG.toReal cG (t/A^2)
    ENNReal.toReal_nonneg hcG (by positivity) htail'
  obtain ⟨D₂,hgeom⟩ := eventually_atTop.1 (source_trial_geometry hA hb ht)
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D α hDD hαlo hαA N K m n _ L hL hn w hw θ hθ v c hc ω cert label hinj himage B hB hBvol hBv
  subst n
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hDD
  have h2 : D₂ ≤ D := (le_max_right _ _).trans hDD
  have hα := hAlo.trans_le hαlo
  rcases hgeom D h2 α hα hαA with
    ⟨hD,hn,hr1,hsmall,hτ,hnscale,hw0,hw1,hwindow,hlarge,hdrift,hdrift',hwin,hrelax,hiso⟩
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < α/D := by positivity
  have hDa : D*(α/D)=α := by field_simp
  have hbnd := sourceHalf_bounds ht hr hD hAlo
    (show Alo ≤ D*(α/D) by rw [hDa]; exact hαlo)
    (show D*(α/D) ≤ A by rw [hDa]; exact hαA)
  obtain ⟨hm,hmH,hel⟩ := eligible_list_size _ _ _ _ _ _ ell θ H D hDp.le hθ _ v ω cert label hinj himage
  obtain ⟨y,z,hyp,hzp,hy,hz,hsepY,hsepZ,hj,hreg,hisoY,hisoZ,hfar⟩ :=
    certificate_trial_geometry hL _ _ _ _ _ _ ell θ H D (by positivity) _ v c hc ω cert label hinj hel hiso
  have hwd : (w:ℝ)=D⁻¹/t := (eq_div_iff ht.ne').mpr (by nlinarith [hw])
  have ey : y=(fun i ↦ nearestLift L c (ω 0 (label i))) := by
    funext i
    exact near_lift_unique hL c (y i) (ω 0 (label i)) (hyp i) (hy i)
  have ez : z=(fun i ↦ nearestLift L c (ω 1 (label i))) := by
    funext i
    exact near_lift_unique hL c (z i) (ω 1 (label i)) (hzp i) (hz i)
  have hmain := hs D α h1 hα hαA L N m _ hn hL hm hmH y z c (fun j ↦ onePathAt j ω) label
    (visitors (gridCenter L v) ω) w B hj hbnd.1 hbnd.2 hr1 hsmall hτ hnscale hw
    hwindow hlarge hdrift hdrift' (by rw [hwd]; exact hwin) hrelax hy hz hsepY hsepZ
    hreg hisoY hisoZ hfar hB hBvol hBv
  simpa only [ey,ez] using hmain

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma labelStartLift_project {N : ℕ} {L : Length} (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (labelStartLift e i)=e.2 i :=
  congrFun (project_representative N L e.2) i

lemma labelEndLift_project {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (labelEndLift t e i)=bridgeEnd N L t e i := by
  ext j
  change ((labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun (labelStartLift_project e i) j
  change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at h
  rw [h]
  rfl

lemma exposed_selected_near {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (hK : 1≤K) (h50 : 50<L.val) (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (p : Fin N→Prop) (b : Fin N→Bool)
    (hb : ∀i : {i // p i},b i=true) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ∀i : {i // p i},‖labelEndLift (2*t) w.1 i-exposedAnchorLift hL w.1 i‖≤3 := by
  filter_upwards [recorded_physical_fiber μ r (2*t)
    (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u)
    (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b p,
    exposed_selected_endpoints hL hK μ m r R C S s₀ (2*t) u p b hb] with w hw he
  intro i
  apply near_end_of_positive_confined h50 (2*t) (labelStartLift w.1 i)
    (labelEndLift (2*t) w.1 i) (exposedAnchorLift hL w.1 i)
    (exposedAnchorLift_near hL hK w.1 i)
  · rw [labelEndLift_project,exposedAnchorLift_project]
    exact (he i).2.1
  · have hs : individualFiber p (noisePairAvoid r (2*t) w.1)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (w.1,β)) b w.2 i ⊆
        {β | ∀s : Time,torusDistance L
          (projectPoint L (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) β s))
          (projectPoint L (exposedAnchorLift hL w.1 i))≤10} := by
      intro β hβ
      have hf := hβ.1
      rw [hb i] at hf
      have ho : ownEligible (K:=K) m r R C S s₀ (2*t) u i (w.1,β) := by
        simpa only [eligibilityFlag,decide_eq_true_eq] using hf
      rw [ownEligible_at hL hK m r R C S s₀ (2*t) u i w.1 β _ (he i)] at ho
      intro s
      rw [exposedAnchorLift_project]
      exact ho.2 s
    exact ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hw.2.1 i)) (measure_mono hs))

def canonicalShift {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  anchorPoint (gridHome hL (e.2 i))-exposedAnchorLift hL e i

lemma canonicalShift_period {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : projectPoint L (canonicalShift hL e i)=0 := by
  ext j
  change (((anchorPoint (gridHome hL (e.2 i)) j-exposedAnchorLift hL e i j):ℝ):AddCircle L.val)=0
  rw [AddCircle.coe_sub]
  exact sub_eq_zero.mpr (congrFun ((anchorPoint_project L _).trans (exposedAnchorLift_project hL e i).symm) j)

lemma canonicalShift_anchor {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) :
    exposedAnchorLift hL e i+canonicalShift hL e i=anchorPoint (gridHome hL (e.2 i)) := by
  unfold canonicalShift
  abel

lemma canonicalShift_start {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (hK : 1≤K) (h50 : 50<L.val) (e : BridgeEndpoints N L) (i : Fin N) :
    labelStartLift e i+canonicalShift hL e i=
      nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i) := by
  apply near_lift_unique h50
  · rw [projectPoint_shift _ (canonicalShift_period hL e i),labelStartLift_project]
  · have he : labelStartLift e i+canonicalShift hL e i-anchorPoint (gridHome hL (e.2 i))=
        labelStartLift e i-exposedAnchorLift hL e i := by unfold canonicalShift; abel
    rw [he]
    exact exposedAnchorLift_near hL hK e i

lemma canonicalShift_end {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (h50 : 50<L.val) (e : BridgeEndpoints N L) (i : Fin N) (t : ℝ)
    (hz : ‖labelEndLift (2*t) e i-exposedAnchorLift hL e i‖≤3) :
    labelEndLift (2*t) e i+canonicalShift hL e i=
      nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i) := by
  apply near_lift_unique h50
  · rw [projectPoint_shift _ (canonicalShift_period hL e i),labelEndLift_project]
  · have he : labelEndLift (2*t) e i+canonicalShift hL e i-anchorPoint (gridHome hL (e.2 i))=
        labelEndLift (2*t) e i-exposedAnchorLift hL e i := by unfold canonicalShift; abel
    rwa [he]

lemma physicalMutual_shift_preimage {I : Type*} {L : Length} (r : ℝ)
    (c : I→Point) (hc : ∀i,projectPoint L (c i)=0) :
    (fun f : I→C(Time,Point) ↦ fun i ↦ Bridge.shiftPath (c i) (f i)) ⁻¹'
      physicalMutual (L:=L) r=physicalMutual (L:=L) r := by
  ext f
  simp only [physicalMutual,pairEvent,mem_preimage,mem_ofPred_eq,project_shift _ (hc _)]
  have he (i j : I) : TrialCollision (L:=L) r (projectCurve L (f j)) (Bridge.shiftPath (c i) (f i)) ↔
      TrialCollision (L:=L) r (projectCurve L (f j)) (f i) := by
    simp only [TrialCollision,Bridge.shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      projectPoint_shift _ (hc i)]
  simp only [he]

lemma canonical_reference_transport {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S t : ℝ) (u : Time) (e : BridgeEndpoints N L)
    (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (hz : ∀i : {i // p i},‖labelEndLift (2*t) e i-exposedAnchorLift hL e i‖≤3) :
    (conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))) (physicalMutual (L:=L) r)).map
      (fun (f : {i // p i} → C(Time,Point)) (i : {i // p i}) ↦ Bridge.shiftPath (canonicalShift hL e i) (f i)) =
    conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t
        (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i))
        (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i))
        (permittedPath m r R C S u
          (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i))
          (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i))
          (anchorPoint (gridHome hL (e.2 i))) (frozenPaths (2*t) e p w)))
      (physicalMutual (L:=L) r) := by
  let μ := fun i : {i // p i} ↦ individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
    (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
      (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))
  have (i : {i // p i}) : IsFiniteMeasure (μ i) := conditioned_finite _ _
  have H := conditioned_pi_map μ (fun i ↦ Bridge.shiftPath (canonicalShift hL e i))
    (fun i ↦ (Bridge.shiftPath_continuous _).measurable) (physicalMutual_measurable (I:={i // p i}) (L:=L) r)
  rw [physicalMutual_shift_preimage (I:={i // p i}) r
    (fun i ↦ canonicalShift hL e i) (fun i ↦ canonicalShift_period hL e i)] at H
  rw [H]
  congr 1
  apply congrArg Measure.pi
  funext i
  have h := individualReference_shift t (labelStartLift e i) (labelEndLift (2*t) e i) (canonicalShift hL e i)
    (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
      (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))
    (permittedPath m r R C S u (labelStartLift e i+canonicalShift hL e i)
      (labelEndLift (2*t) e i+canonicalShift hL e i)
      (exposedAnchorLift hL e i+canonicalShift hL e i) (frozenPaths (2*t) e p w))
    (permittedPath_measurable ..)
    (permittedPath_shift m r R C S u _ _ _ _ (canonicalShift_period hL e i) _)
  simpa only [canonicalShift_start hL hK h50,canonicalShift_end hL h50 e i t (hz i),
    canonicalShift_anchor] using h

theorem actual_allocated_canonical_reference {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ((fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b))) w).map
        (fun β (i : {i // p i}) ↦ Bridge.shiftPath (canonicalShift hL w.1 i)
          (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))) =
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        individualReference t
          (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
          (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L (2*t) w.1 i))
          (permittedPath m r R C S u
            (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
            (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L (2*t) w.1 i))
            (anchorPoint (gridHome hL (w.1.2 i))) (frozenPaths (2*t) w.1 p w.2)))
        (physicalMutual (L:=L) r) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let base := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  by_cases hb : ∀i : {i // p i},b i=true
  · have hn := exposed_selected_near hL hK h50 base m r R C S s₀ t u p b hb
    have hd : (fun i ↦ Classical.propDecidable (p i)) =
        (fun i ↦ Finset.decidableMem i (groupUnion g a)) := Subsingleton.elim _ _
    rw [hd] at hn
    filter_upwards [actual_allocated_physical_reference hL hK h50 μ m r R C S s₀ t u g b a,
      hn] with w hw hz
    have H := canonical_reference_transport hL hK h50 m r R C S t u w.1 p w.2 hz
    rw [←hw] at H
    have hm : Measurable (fun β : {i // p i}→Bridge.Noise ↦ fun i : {i // p i} ↦
        leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i)) :=
      Measurable.of_eval (fun i ↦ (leg_continuous (2*t) _ _).measurable.comp (measurable_pi_apply i))
    have hc : Measurable (fun f : {i // p i}→C(Time,Point) ↦ fun i : {i // p i} ↦
        Bridge.shiftPath (canonicalShift hL w.1 i) (f i)) := by fun_prop
    rw [Measure.map_map hc hm] at H
    have hC : MeasurableSet (blockEvent p (labelInteraction N L r (2*t)∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)) :=
      ((labelInteraction_measurable N L r (2*t)).inter
        (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)).preimage
          (blockGlue_measurable p)
    have he : fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)) w =
        conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
          {β | blockGlue p (w,β) ∈ labelInteraction N L r (2*t)∩
            flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b} := by
      change (fiberRestrict _ _ w univ)⁻¹ • fiberRestrict _ _ w=_
      rw [fiberRestrict_apply _ hC]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,conditionedMeasure]
      rfl
    rw [he]
    convert H using 1 <;> congr 10
    all_goals try exact Subsingleton.elim _ _
    all_goals rw [hd]
  · filter_upwards [allocated_selected_flags hL μ g b a
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)] with w hw
    exact (hb (fun i ↦ hw i i.property)).elim

end HardSphere.Groups
end
end

end OAI
