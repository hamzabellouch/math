import OAI.MeasureTheory.Falconer.Recursion.DescriptorMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_descriptor_good_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ)
        (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ P : CellPath, P.length = descriptorAnchor b → ∀ ω ω' : UnitCircle,
      dist ω ω' ≤ sourceAngularRadius N sig (descriptorLength b) →
      ω ∈ descriptorGoodSet Q ρ m N lam sig J i P b →
      ω' ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_parallel_width_transfer hsig hJ (C₀ := 1) zero_le_one
  obtain ⟨N₂,h₂⟩ := uniform_projection_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ m lam i b hb P hP ω ω' hd hg
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN
  change dist (ω:Plane) (ω':Plane) ≤ _ at hd
  cases b with
  | parallel g p =>
    dsimp only [descriptorGoodSet,parallelGoodSet,Set.mem_ofPred_eq] at hg ⊢
    change (_ : ℝ) ≤ _ at hg ⊢
    apply le_trans (Nat.cast_le.mpr (h₁ N hN₁
      Q ρ g p hb.1 P i ω ω' (by simpa only [descriptorLength,one_mul] using hd))) hg
  | projection p u =>
    dsimp only [descriptorGoodSet,projectionGoodSet,Set.mem_ofPred_eq] at hg ⊢
    change (_ : ℝ) ≤ _ at hg ⊢
    apply le_trans (Nat.cast_le.mpr (h₂ N hN₂
      Q hQ ρ p u hb.1 P hP i ω ω' (by simpa only [descriptorLength,one_mul] using hd))) hg

end PlanarFalconer

end OAI
