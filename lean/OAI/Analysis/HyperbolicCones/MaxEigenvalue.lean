import OAI.Analysis.HyperbolicCones.NormThreshold

namespace OAI

/-! On the positive cone, the largest eigenvalue is the operator norm, including zero. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem posSemidef_norm_isGreatest {n : ℕ} [NeZero n]
    (A : Mat n ℝ) (hA : A.PosSemidef) : IsGreatest (spectrum ℝ A) ‖A‖ := by
  have hgreat := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum
    (𝕜 := ℝ) (p := IsSelfAdjoint) A hA.isHermitian
  constructor
  · obtain ⟨x, hx, hnorm⟩ := hgreat.1
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    have heq : ‖A‖ = x := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hnorm.symm
    rwa [heq]
  · intro x hx
    exact (le_abs_self x).trans (hgreat.2 ⟨x, hx, rfl⟩)

theorem posSemidef_largestEigenvalue_tendsto {n : ℕ} [NeZero n]
    {T : Type u} {L : Filter T} {A : T → Mat n ℝ} {A₀ : Mat n ℝ}
    (hA : ∀ t, (A t).PosSemidef) (hA₀ : A₀.PosSemidef)
    (hlim : Tendsto A L (𝓝 A₀)) (eig : T → ℝ) (eig₀ : ℝ)
    (heig : ∀ t, IsGreatest (spectrum ℝ (A t)) (eig t))
    (heig₀ : IsGreatest (spectrum ℝ A₀) eig₀) : Tendsto eig L (𝓝 eig₀) := by
  have heq : eig = fun t => ‖A t‖ := funext fun t =>
    (heig t).unique (posSemidef_norm_isGreatest (A t) (hA t))
  have heq₀ : eig₀ = ‖A₀‖ := heig₀.unique (posSemidef_norm_isGreatest A₀ hA₀)
  rw [heq, heq₀]
  exact hlim.norm

end Paper256

end

end OAI
