import OAI.MeasureTheory.Falconer.Recursion.DescriptorMasks

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem descriptor_mask_failure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ) (ha : SourceAngularBounds Q ρ m N lam sig)
    {b : PolicyDescriptor} (hb : ValidDescriptor N b) {x : Plane}
    (hx : ∃ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b), x ∈ (Q.descendant P).carrier) :
    sourceArcLength {dir | descriptorSpatialMask Q ρ m N lam sig J 0 b x dir ≠ 1} ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨P,hP,hx⟩ := hx
  simp only [descriptorSpatialMask,spatialAnchorMask_eq Q hQ ρ _ _ _ _ hP hx]
  apply (circleTestMask_failure_le _ (measurable_descriptorGoodSet _ _ _ _ _ _ _ _ _ _) _ _).trans
  exact descriptorGoodSet_exceptional Q ρ m N lam sig J ha hb
    ((mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1)

theorem listMask_failure_subset (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) :
    {dir | descriptorListMask Q ρ m N lam sig J i S x dir ≠ 1} ⊆
      ⋃ b ∈ S, {dir | descriptorSpatialMask Q ρ m N lam sig J i b x dir ≠ 1} := by
  intro dir hdir
  by_contra hn
  have hh : ∀ b ∈ S, descriptorSpatialMask Q ρ m N lam sig J i b x dir = 1 := by
    intro b hb
    by_contra h
    exact hn (mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,h⟩⟩)
  exact hdir (by simp only [descriptorListMask,Finset.prod_eq_one hh])

theorem ae_listMask_failure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (hcarry : ρ Q.carrierᶜ = 0) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ)
    (ha : SourceAngularBounds Q ρ m N lam sig) (S : Finset PolicyDescriptor)
    (hS : ∀ b ∈ S, ValidDescriptor N b) :
    ∀ᵐ x ∂ρ, sourceArcLength {dir | descriptorListMask Q ρ m N lam sig J 0 S x dir ≠ 1} ≤
      (S.card:ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  have hx : ∀ᵐ x ∂ρ, ∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor Q ρ hcarry n)
  filter_upwards [hx] with x hx
  apply (measure_mono (listMask_failure_subset Q ρ m N lam sig J 0 S x)).trans
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ S, ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
      apply Finset.sum_le_sum
      intro b hb
      exact descriptor_mask_failure_bound Q hQ ρ m N lam sig J ha (hS b hb) (hx _)
    _ = _ := by simp

end PlanarFalconer

end OAI
