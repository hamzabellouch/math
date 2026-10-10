import OAI.MeasureTheory.Falconer.Angular.InheritedAngularSymbols

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem uniform_descriptorAngleMask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : DyadicSquare, Q.side = 1 →
    ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ) (b : PolicyDescriptor),
    ValidDescriptor N b → ∀ (P : CellPath), P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b) →
    ∀ x ∈ (Q.descendant P).carrier,
    tsupport (descriptorAngleMask Q ρ m N lam sig J i b x) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_parallel_mask_support hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_projection_mask_support hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ m lam i b hb P hP x hx
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have he : descriptorAngleMask Q ρ m N lam sig J i b x =
      sourceTestMask (descriptorGoodSet Q ρ m N lam sig J i P b)
        (sourceAngularRadius N sig (descriptorLength b)) (sourceAngularRadius_pos _ _ _) := by
    funext θ
    exact (spatialAnchorMask_eq Q hQpos ρ _ _ _ _ hP hx _).trans (circleTestMask_comp _ _ _ _)
  rw [he]
  have hlen := (mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1
  cases b with
  | parallel g p => exact h₁ N ((le_max_left _ _).trans hN) Q ρ g p hb.1 P i _
  | projection p u => exact h₂ N ((le_max_right _ _).trans hN) Q hQ ρ p u hb.1 P hlen i _

 theorem uniform_inheritedMaskProduct_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (x : ι → Plane) (j : ℕ),
    ∀ a ∈ S, ValidDescriptor N (b a) → ∀ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)),
    x a ∈ (Q.descendant P).carrier →
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorAngleMask_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i x j a ha hb P hP hx
  exact (inheritedMaskProduct_support S b k Q ρ m N lam sig J i x ha j).trans
    (h₀ N hN Q hQ ρ m lam i (b a) hb P hP (x a) hx)

end PlanarFalconer

end OAI
