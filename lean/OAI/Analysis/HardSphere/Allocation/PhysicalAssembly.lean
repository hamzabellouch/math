import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalReference
import OAI.Analysis.HardSphere.Geometry.SiteGroups

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace HardSphere.Comparison

lemma finite_allocation_joint {E A : Type*} [MeasurableSpace E]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure E) [SFinite μ] (κ : Kernel E A) [IsSFiniteKernel κ] :
    (∑ a, (μ.withDensity (fun e ↦ κ e {a})).map (fun e ↦ (e,a))) = μ.compProd κ := by
  classical
  ext B hB
  rw [Measure.finsetSum_apply, Measure.compProd_apply hB]
  let F : A → E → ℝ≥0∞ := fun a ↦
    ((fun e ↦ (e,a)) ⁻¹' B).indicator (fun e ↦ κ e {a})
  have hF (a : A) : Measurable (F a) :=
    (κ.measurable_coe (measurableSet_singleton a)).indicator
      (hB.preimage measurable_prodMk_right)
  trans ∑ a, ∫⁻ e, F a e ∂μ
  · apply Finset.sum_congr rfl
    intro a _
    rw [Measure.map_apply measurable_prodMk_right hB,
      withDensity_apply _ (hB.preimage measurable_prodMk_right)]
    exact (lintegral_indicator (hB.preimage measurable_prodMk_right) _).symm
  rw [← lintegral_finsetSum _ (fun a _ ↦ hF a)]
  apply lintegral_congr
  intro e
  rw [← lintegral_indicator_one (hB.preimage measurable_prodMk_left), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (e,a) ∈ B <;> simp [F, h]

lemma recorded_density_sum {E J : Type*} [MeasurableSpace E]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure E) (r : E → J) (hr : Measurable r)
    (f : J → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    (∑ j, (μ.withDensity (f j)).restrict {e | r e = j}) =
      μ.withDensity (fun e ↦ f (r e) e) := by
  classical
  have hset (j : J) : MeasurableSet {e | r e = j} :=
    measurableSet_eq_fun hr measurable_const
  have h := withDensity_tsum (μ := μ)
    (fun j ↦ (hf j).indicator (hset j))
  rw [Measure.sum_fintype] at h
  have heq : (∑' j, {e | r e = j}.indicator (f j)) = (fun e ↦ f (r e) e) := by
    funext e
    rw [tsum_fintype, Finset.sum_apply]
    simp [Set.indicator]
  rw [heq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [restrict_withDensity (hset j), withDensity_indicator (hset j)]

lemma allocated_flag_joint {E Y J A : Type*}
    [MeasurableSpace E] [MeasurableSpace Y]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure E) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (κ : Kernel (E × J) A) [IsSFiniteKernel κ]
    (r : E × Y → J) (hr : Measurable r)
    {B : Set (E × Y)} (hB : MeasurableSet B) :
    (∑ b, ∑ a, (((μ.withDensity (fun e ↦ κ (e,b) {a})).prod ν).restrict
      (B ∩ {z | r z = b})).map (fun z ↦ (z,a))) =
      ((μ.prod ν).restrict B).compProd
        (κ.comap (fun z ↦ (z.1,r z)) (measurable_fst.prodMk hr)) := by
  classical
  let μB := (μ.prod ν).restrict B
  have hm (b : J) (a : A) : Measurable (fun e : E ↦ κ (e,b) {a}) :=
    (κ.measurable_coe (measurableSet_singleton a)).comp measurable_prodMk_right
  have hs (b : J) : MeasurableSet {z : E × Y | r z = b} :=
    measurableSet_eq_fun hr measurable_const
  have hd (a : A) :
      (∑ b, ((μ.withDensity fun e ↦ κ (e,b) {a}).prod ν).restrict
        (B ∩ {z | r z = b})) = μB.withDensity (fun z ↦ κ (z.1,r z) {a}) := by
    trans ∑ b, (μB.withDensity (fun z ↦ κ (z.1,b) {a})).restrict {z | r z = b}
    · apply Finset.sum_congr rfl
      intro b _
      rw [prod_withDensity_left (hm b a), restrict_withDensity (hB.inter (hs b)),
        restrict_withDensity (hs b)]
      congr 1
      simp only [μB, Measure.restrict_restrict (hs b), Set.inter_comm]
    · exact recorded_density_sum μB r hr _ (fun b ↦ (hm b a).comp measurable_fst)
  rw [Finset.sum_comm]
  trans ∑ a, (μB.withDensity (fun z ↦ κ (z.1,r z) {a})).map (fun z ↦ (z,a))
  · apply Finset.sum_congr rfl
    intro a _
    rw [← Measure.map_finset_sum' measurable_prodMk_right.aemeasurable, hd a]
  · exact finite_allocation_joint μB
      (κ.comap (fun z ↦ (z.1,r z)) (measurable_fst.prodMk hr))

lemma map_retained_compProd {E F A : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace A]
    (μ : Measure E) [SFinite μ] (f : E → F) (hf : Measurable f)
    (κ : Kernel F A) [IsSFiniteKernel κ] :
    (μ.compProd (κ.comap f hf)).map (fun z ↦ (f z.1,z.2)) =
      (μ.map f).compProd κ := by
  ext B hB
  have hmap : Measurable (fun z : E × A ↦ (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hmap hB, Measure.compProd_apply (hB.preimage hmap),
    Measure.compProd_apply hB,
    lintegral_map (κ.measurable_kernel_prodMk_left hB) hf]
  rfl

end HardSphere.Comparison

namespace HardSphere.Comparison
variable {E I A : Type*} [MeasurableSpace E] [Fintype I]
variable {X : I → Type*} [∀ i, MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

lemma allocated_exposure_joint [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (μ : Measure E) [SFinite μ] (ν : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (ν i)]
    (flag : ∀ i, E × X i → Bool) (hflag : ∀ i, Measurable (flag i))
    (κ : Kernel (E × (I → Bool)) A) [IsMarkovKernel κ] (p : A → I → Prop)
    {B : Set (E × (∀ i, X i))} (hB : MeasurableSet B) :
    (∑ b, ∑ a, ((exposedLaw (allocationBase μ κ b a) ν (p a)
        (B ∩ flagEvent flag b)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p a i} ↦ ν i))
        (blockEvent (p a) (B ∩ flagEvent flag b)))).map
          (fun z ↦ (blockGlue (p a) z, a))) =
      ((μ.prod (Measure.pi ν)).restrict B).compProd
        (κ.comap (fun z ↦ (z.1, fun i ↦ flag i (z.1,z.2 i)))
          (measurable_fst.prodMk (Measurable.of_eval (fun i ↦
            (hflag i).comp (measurable_fst.prodMk
              ((measurable_pi_apply i).comp measurable_snd)))))) := by
  have (b : I → Bool) (a : A) :
      SFinite (exposedLaw (allocationBase μ κ b a) ν (p a) (B ∩ flagEvent flag b)) := by
    unfold exposedLaw
    infer_instance
  trans ∑ b, ∑ a, (((allocationBase μ κ b a).prod (Measure.pi ν)).restrict
    (B ∩ flagEvent flag b)).map (fun z ↦ (z,a))
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    have h := congrArg (fun m ↦ m.map (fun z : E × (∀ i, X i) ↦ (z,a)))
      (exposed_block_reconstruct (allocationBase μ κ b a) ν (p a)
        (hB.inter (flagEvent_measurable flag hflag b)))
    simpa only [Measure.map_map measurable_prodMk_right (blockGlue_measurable (p a)),
      Function.comp_def] using h
  · simpa only [allocationBase, flagEvent, funext_iff] using
      allocated_flag_joint μ (Measure.pi ν) κ
        (fun z i ↦ flag i (z.1,z.2 i))
        (Measurable.of_eval (fun i ↦ (hflag i).comp
          (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))) hB

lemma allocationBase_ae_support {E J A : Type*} [MeasurableSpace E]
    [MeasurableSpace J] [Fintype J] [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (μ : Measure E) (κ : Kernel (E × J) A)
    (b : J) (a : A) (P : E → A → Prop)
    (hP : ∀ e, ∀ᵐ a' ∂κ (e,b), P e a') :
    ∀ᵐ e ∂allocationBase μ κ b a, P e a := by
  apply (ae_withDensity_iff ((κ.measurable_coe (measurableSet_singleton a)).comp
    (measurable_id.prodMk measurable_const))).mpr
  apply ae_of_all
  intro e hn
  by_contra h
  apply hn
  exact measure_mono_null (by simpa only [singleton_subset_iff, mem_ofPred_eq] using h)
    (ae_iff.mp (hP e))

lemma exposed_endpoint_ae {E I : Type*} [MeasurableSpace E] [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure E) [SFinite μ] (ν : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (ν i)] (p : I → Prop) [DecidablePred p]
    (B : Set (E × (∀ i, X i))) {P : E → Prop} (hP : ∀ᵐ e ∂μ, P e) :
    ∀ᵐ w ∂exposedLaw μ ν p B, P w.1 := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact Measure.quasiMeasurePreserving_fst.ae hP

end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital GaussianPacking
attribute [local instance] Classical.propDecidable

lemma recorded_allocation_is_physical {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (μ : Measure (BridgeEndpoints N L))
    (m q : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      gridAllocationKernel hL q
        (z.1, fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ t u i (z.1,z.2 i)) =
      physicalAllocationKernel (K:=K) m q r R C S s₀ u (labelBridgePath N L t z) := by
  have he : ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L t z 0 = z.1.2 ∧
      labelBridgePath N L t z 1 = bridgeEnd N L t z.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun ((continuous_eval_const (0:Time)).measurable.comp
          (labelBridgePath_measurable N L t)) measurable_fst.snd).inter
        (measurableSet_eq_fun ((continuous_eval_const (1:Time)).measurable.comp
          (labelBridgePath_measurable N L t))
          ((bridgeEnd_continuous N L t).measurable.comp measurable_fst)))).mpr
    exact ae_of_all _ (exposed_endpoints t)
  filter_upwards [he] with z hz
  rw [gridAllocationKernel_apply, physicalAllocationKernel, Kernel.comap_apply]
  change Measure.pi _ = Measure.pi _
  congr 1
  funext v
  rw [recordedList_eq hL hK m r R C S s₀ t u v z.1 z.2 hz.1 hz.2]

lemma genuine_ground_allocated_joint {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (ψ : Jet N L) (m q : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : GridAllocation N K q → Fin N → Prop) :
    (∑ b, ∑ a, ((exposedLaw
        (allocationBase (endpointWeightedBase ψ t) (gridAllocationKernel hL q) b a)
        (fun _ : Fin N ↦ Bridge.law) (p a)
        (labelInteraction N L r t ∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ t u) b)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p a i} ↦ Bridge.law))
        (blockEvent (p a) (labelInteraction N L r t ∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ t u) b)))).map
        (fun z ↦ (labelBridgePath N L t (blockGlue (p a) z),a))) =
      (groundPathLaw N L r t ψ).compProd
        (physicalAllocationKernel (K:=K) m q r R C S s₀ u) := by
  let flag := eligibilityFlag (N:=N) (K:=K) (L:=L) m r R C S s₀ t u
  have hflag : ∀ i, Measurable (flag i) :=
    fun i ↦ eligibilityFlag_measurable m r R C S s₀ t u i
  let base := ((endpointWeightedBase ψ t).prod
    (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict (labelInteraction N L r t)
  have hf : Measurable (fun z : (BridgeEndpoints N L × (Fin N → Bridge.Noise)) ×
      GridAllocation N K q ↦ (labelBridgePath N L t z.1,z.2)) :=
    ((labelBridgePath_measurable N L t).comp measurable_fst).prodMk measurable_snd
  have h := congrArg (fun μ ↦ μ.map
    (fun z : (BridgeEndpoints N L × (Fin N → Bridge.Noise)) × GridAllocation N K q ↦
      (labelBridgePath N L t z.1,z.2)))
    (allocated_exposure_joint (endpointWeightedBase ψ t)
      (fun _ : Fin N ↦ Bridge.law) flag hflag (gridAllocationKernel hL q) p
      (labelInteraction_measurable N L r t))
  simp only [Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_map hf ((blockGlue_measurable _).prodMk measurable_const),
    Function.comp_def] at h
  have hκ : ∀ᵐ z ∂base,
      ((gridAllocationKernel hL q).comap
        (fun z ↦ (z.1, fun i ↦ flag i (z.1,z.2 i)))
        (measurable_fst.prodMk (Measurable.of_eval (fun i ↦
          (hflag i).comp (measurable_fst.prodMk
            ((measurable_pi_apply i).comp measurable_snd)))))) z =
      ((physicalAllocationKernel (K:=K) m q r R C S s₀ u).comap
        (labelBridgePath N L t) (labelBridgePath_measurable N L t)) z := by
    simpa only [Kernel.comap_apply] using
      (ae_restrict_of_ae (s:=labelInteraction N L r t)
        (recorded_allocation_is_physical hL hK
          (endpointWeightedBase ψ t) m q r R C S s₀ t u))
  rw [Measure.compProd_congr hκ] at h
  rw [map_retained_compProd base (labelBridgePath N L t)
    (labelBridgePath_measurable N L t)
    (physicalAllocationKernel (K:=K) m q r R C S s₀ u)] at h
  rw [show base.map (labelBridgePath N L t) = groundPathLaw N L r t ψ from
    genuine_ground_label_bridge ψ r t] at h
  convert h using 1
  congr 2
  exact Subsingleton.elim _ _

lemma allocated_selected_flags {N K M G : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N → Bool) (a : GridAllocation N K (G*M))
    (B : Set (BridgeEndpoints N L × (Fin N → Bridge.Noise))) :
    ∀ᵐ _ ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i ∈ groupUnion g a) B,
        ∀ i ∈ groupUnion g a, b i = true := by
  apply exposed_endpoint_ae
    (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i ∈ groupUnion g a) B
    (P:=fun _ ↦ ∀ i ∈ groupUnion g a, b i = true)
  filter_upwards [allocationBase_ae_support μ (gridAllocationKernel hL (G*M)) b a
    (fun e a' ↦ ∀ v, a' v ∈ (allocationPMF (recordedList hL v (e,b)) (G*M)).support)
    (fun e ↦ gridAllocation_support_ae hL (G*M) (e,b))] with e he
  intro i hi
  obtain ⟨v, _, hiv⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp (groupAt_mem_list hL (e,b) a he g v hiv)).2.2

lemma true_flag_endpoint {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (e : BridgeEndpoints N L) (β : Bridge.Noise)
    (hb : eligibilityFlag (K:=K) m r R C S s₀ t u i (e,β) = true) :
    EndpointEligible (gridHome hL (e.2 i)) s₀ e.2 (bridgeEnd N L t e) i := by
  have ho : ownEligible (K:=K) m r R C S s₀ t u i (e,β) :=
    of_decide_eq_true hb
  obtain ⟨v, hv, _⟩ := ho
  rwa [(gridHome_eq_iff hL hK _ _).mpr hv.1]

lemma exposed_selected_endpoints {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool)
    (hb : ∀ i : {i // p i}, b i = true) :
    ∀ᵐ w ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r t ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ t u) b),
      ∀ i : {i // p i}, EndpointEligible (gridHome hL (w.1.2 i))
        s₀ w.1.2 (bridgeEnd N L t w.1) i := by
  filter_upwards [exposed_block_positive μ (fun _ : Fin N ↦ Bridge.law) p
    ((labelInteraction_measurable N L r t).inter
      (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ t u i) b))]
    with w hw
  obtain ⟨β,hβ⟩ := nonempty_of_measure_ne_zero hw.ne'
  intro i
  apply true_flag_endpoint hL hK m r R C S s₀ t u i w.1 (β i)
  have hflag := hβ.2 i
  simpa only [blockGlue_fst, blockGlue_inside, hb i] using hflag

def exposedAnchorLift {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : Point :=
  nearestLift L (labelStartLift e i) (gridCenter L (gridHome hL (e.2 i)))

lemma exposedAnchorLift_project {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (exposedAnchorLift hL e i) = gridCenter L (gridHome hL (e.2 i)) :=
  nearestLift_project ..

lemma exposedAnchorLift_near {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (hK : 1 ≤ K) (e : BridgeEndpoints N L) (i : Fin N) :
    ‖labelStartLift e i - exposedAnchorLift hL e i‖ ≤ 3 := by
  rw [norm_sub_rev]
  change ‖nearestLift L (labelStartLift e i) _ - labelStartLift e i‖ ≤ 3
  refine (nearestLift_bound L _ _ (R:=1) ?_).trans (by norm_num)
  have he : projectPoint L (labelStartLift e i) = e.2 i := by
    exact congrFun (project_representative N L e.2) i
  rw [he]
  simpa only [torusDistance, dist_comm] using centeredCell_distance (gridHome_mem hL hK (e.2 i))

def ExposedPhysicalIdentity {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool)
    (w : BridgeEndpoints N L × ({i // ¬p i} → Bridge.Noise)) : Prop :=
(conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
  {β | blockGlue p (w,β) ∈ labelInteraction N L r (2*t) ∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b}).map
  (fun β (i : {i // p i}) ↦
    leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i)) =
conditionedMeasure (Measure.pi fun i : {i // p i} ↦
  individualReference t (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
    (permittedPath m r R C S u (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
      (exposedAnchorLift hL w.1 i) (frozenPaths (2*t) w.1 p w.2)))
  (physicalMutual (L:=L) r)

lemma canonical_physical_reference {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool) (hb : ∀i : {i // p i}, b i = true) :
    ∀ᵐ w ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ExposedPhysicalIdentity hL m r R C S s₀ t u p b w := by
  unfold ExposedPhysicalIdentity
  filter_upwards [physical_recorded_reference hL hK h50 μ m r R C S s₀ t u p b hb,
    exposed_selected_endpoints hL hK μ m r R C S s₀ (2*t) u p b hb] with w hw he
  exact hw (fun i ↦ gridHome hL (w.1.2 i)) (fun i ↦ exposedAnchorLift hL w.1 i)
    (fun i ↦ exposedAnchorLift_project hL w.1 i)
    (fun i ↦ exposedAnchorLift_near hL hK w.1 i) he

theorem actual_allocated_physical_reference {N K M G : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N → Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i ∈ groupUnion g a
    ∀ᵐ w ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ExposedPhysicalIdentity hL m r R C S s₀ t u p b w := by
  dsimp only
  let p := fun i ↦ i ∈ groupUnion g a
  let base := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  by_cases hb : ∀ i : {i // p i}, b i = true
  · have h := canonical_physical_reference hL hK h50 base m r R C S s₀ t u p b hb
    have hd : (fun i ↦ Classical.propDecidable (p i)) =
        (fun i ↦ Finset.decidableMem i (groupUnion g a)) := Subsingleton.elim _ _
    rw [hd] at h
    exact h
  · filter_upwards [allocated_selected_flags hL μ g b a
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)] with w hw
    exact (hb (fun i ↦ hw i i.property)).elim

end HardSphere.Groups
end
end

end OAI
