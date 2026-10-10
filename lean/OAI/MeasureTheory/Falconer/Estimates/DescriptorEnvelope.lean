import OAI.MeasureTheory.Falconer.Angular.AngularEnvelopeGraph
import OAI.MeasureTheory.Falconer.Graphs.DescriptorGraph
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState

namespace OAI

/-! # The actual descriptor tests used by the angular envelope

These are finite intersections of the original endpoint tests. Passing to
retained lists only weakens these support conditions. No deletion of an
angular factor or analytic estimate is inferred from this set inclusion.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDescriptorList remainingPolicyDescriptors)

variable {d : ℕ}

def descriptorListGood (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    Set (Space d × Sphere d) :=
  {z | ∀ b ∈ B, z ∈ descriptorEndpointGood Q ρ m N σ J i b}

theorem descriptorListGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) :
    MeasurableSet (descriptorListGood Q ρ m N σ J i B) := by
  have h := Finset.measurableSet_biInter B (fun b _ =>
    descriptorEndpointGood_measurable Q ρ m N σ J i b)
  convert h using 1
  ext z
  simp only [descriptorListGood,mem_ofPred_eq,mem_iInter]

theorem descriptorListGood_antitone (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {B C : Finset PolicyDescriptor} (hCB : C ⊆ B) :
    descriptorListGood Q ρ m N σ J i B ⊆ descriptorListGood Q ρ m N σ J i C :=
  fun _ hz b hb => hz b (hCB hb)

theorem policy_descriptorListGood_mono (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (A : ℕ → ℝ)
    {q a a' t t' : ℕ} (ha : a ≤ a') (ht : t' ≤ t) :
    descriptorListGood Q ρ m N σ J i (policyDescriptorList A N q a t) ⊆
      descriptorListGood Q ρ m N σ J i (policyDescriptorList A N q a' t') :=
  descriptorListGood_antitone Q ρ m N σ J i (PlanarFalconer.policyDescriptorList_mono A ha ht)

theorem remaining_descriptorListGood_mono (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (A : ℕ → ℝ)
    (q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    descriptorListGood Q ρ m N σ J i (remainingPolicyDescriptors A N q a₀ t₀ a) ⊆
      descriptorListGood Q ρ m N σ J i (remainingPolicyDescriptors A N q a₀ t₀ p) :=
  descriptorListGood_antitone Q ρ m N σ J i
    (PlanarFalconer.remainingPolicyDescriptors_mono A N q a₀ t₀ hap)

theorem minimal_policy_descriptorListGood (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (A : ℕ → ℝ)
    {q a₀ t₀ a b v : ℕ} (hq : 0 < q) (hleft : a₀ ≤ b) (hright : v ≤ t₀)
    (hdepth : a ≤ b) :
    descriptorListGood Q ρ m N σ J i (remainingPolicyDescriptors A N q a₀ t₀ a) ⊆
      descriptorListGood Q ρ m N σ J i (policyDescriptorList A N q b v) :=
  descriptorListGood_antitone Q ρ m N σ J i
    (PlanarFalconer.minimal_policy_list_survives A hq hleft hright hdepth)

/-- This uses the continuous profile at the actual normalized integer depths. -/
theorem descriptorListGood_parallel_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (hB : PolicyDescriptor.parallel g p ∈ B)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier)
    (w : Sphere d)
    (hw : (x,w) ∈ descriptorListGood Q ρ (fun t => m (t/N)) N σ J i B) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J i p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun j : ℕ => m ((j:ℝ)/N)-((d:ℝ)/2)*(j:ℝ)/N) g p+
          1000*((d:ℝ)+1)*σ)⌉₊ :=
  descriptorEndpointGood_graph_test Q hQ ρ (fun t => m (t/N)) N σ J i
    hag hgp X P hX hP hx w (hw _ hB)

/-- The origin chosen by the scalar policy is among its actual descriptor list. -/
theorem originDescriptors_subset_policy (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hwide : a+100*q < t) :
    PlanarFalconer.originDescriptors A N q a t ⊆ policyDescriptorList A N q a t := by
  intro b hb
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,hb⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,Finset.mem_range.mpr ?_⟩,
    le_rfl,le_rfl,hwide⟩ <;> omega

theorem originDescriptors_subset_remaining (A : ℕ → ℝ)
    {N q a₀ t₀ a b v : ℕ} (hq : 0 < q) (hv : v ≤ N)
    (hwide : b+100*q < v) (hleft : a₀ ≤ b) (hright : v ≤ t₀) (hdepth : a ≤ b) :
    PlanarFalconer.originDescriptors A N q b v ⊆
      remainingPolicyDescriptors A N q a₀ t₀ a :=
  (originDescriptors_subset_policy A hv hwide).trans
    (PlanarFalconer.minimal_policy_list_survives A hq hleft hright hdepth)

theorem origin_parallel_mem_remaining (A : ℕ → ℝ)
    {N q a₀ t₀ a b v g : ℕ} (hq : 0 < q) (hv : v ≤ N)
    (hwide : b+100*q < v) (hleft : a₀ ≤ b) (hright : v ≤ t₀) (hdepth : a ≤ b)
    (hg : g ∈ Finset.Ico
      (PlanarFalconer.policyDepth A N q b v-
        min (PlanarFalconer.policyDepth A N q b v-b) (v-PlanarFalconer.policyDepth A N q b v))
      (PlanarFalconer.policyDepth A N q b v)) :
    PolicyDescriptor.parallel g (PlanarFalconer.policyDepth A N q b v) ∈
      remainingPolicyDescriptors A N q a₀ t₀ a := by
  apply originDescriptors_subset_remaining A hq hv hwide hleft hright hdepth
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)

/-- List support may be weakened while preserving the same analytic symbol budget. -/
theorem AngularAdmissible.descriptorList_subset {n k : ℕ} {D : ℝ}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {B C : Finset PolicyDescriptor} (hCB : C ⊆ B)
    {b : Space (n+2) → Sphere (n+2) → ℂ}
    (hb : AngularAdmissible k D (descriptorListGood Q ρ m N σ J i B) b) :
    AngularAdmissible k D (descriptorListGood Q ρ m N σ J i C) b :=
  ⟨hb.1,fun x w hx => descriptorListGood_antitone Q ρ m N σ J i hCB (hb.2 x w hx)⟩

end Falconer

end OAI
