import OAI.Geometry.SingularHomology.HomologyNaturality

namespace OAI

noncomputable section

namespace Problem340

variable {X : Type} [TopologicalSpace X]
  {f g : X → X} (hf : Continuous f) (hg : Continuous g)

theorem homologyRadiusSet_eq_of_homotopy
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n f hf u = a • u - b • v ∧
      realHomologyMap n f hf v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} =
    {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n g hg u = a • u - b • v ∧
      realHomologyMap n g hg v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  ext r
  simp only [realHomologyMap_eq_of_homotopy _ hf hg H]

theorem totalRealHomologySpectralRadius_eq_of_homotopy
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    totalRealHomologySpectralRadius f hf = totalRealHomologySpectralRadius g hg := by
  unfold totalRealHomologySpectralRadius
  exact congrArg sSup (homologyRadiusSet_eq_of_homotopy hf hg H)

theorem totalRealHomologySpectralRadius_eq_of_homotopic
    (H : ContinuousMap.Homotopic (continuousMapOf f hf) (continuousMapOf g hg)) :
    totalRealHomologySpectralRadius f hf = totalRealHomologySpectralRadius g hg := by
  obtain ⟨H⟩ := H
  exact totalRealHomologySpectralRadius_eq_of_homotopy hf hg H

theorem homologyRadiusSet_bddAbove_iff_of_homotopy
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    BddAbove {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n f hf u = a • u - b • v ∧
      realHomologyMap n f hf v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} ↔
    BddAbove {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n g hg u = a • u - b • v ∧
      realHomologyMap n g hg v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  rw [homologyRadiusSet_eq_of_homotopy hf hg H]

end Problem340

end

end OAI
