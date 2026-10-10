import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariancePath
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteSpectralIntegral

namespace OAI

/-! Entrywise conversion of the actual finite spectral Gaussian
covariances to the weighted spectral resolvent and its derivative. -/

noncomputable section
open MeasureTheory Set IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

variable {m d : ℕ}

lemma cavity_finite_covariance_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {x : ℝ} (hx : 0 < x) (i j : Fin d) :
    rho (g i) * cavityFiniteCovariance rho lam hrho hsum g x i j =
      if i = j then projectedResolvent rho lam hrho hsum (g i) x else 0 := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  by_cases hij : i = j
  · subst j
    simp [projectedResolvent, hx, div_eq_mul_inv]
  · simp [hij]

lemma cavity_finite_root_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {n : ℕ} (p : OverlapPath) (q : Fin (n + 1) → ℝ)
    (hx : 0 < deficit p (q 0)) (i j : Fin d) :
    rho (g i) * cavityFiniteRootCovariance rho lam hrho hsum g p q i j =
      if i = j then q 0 * projectedResolventDerivative rho lam hrho hsum (g i)
        (deficit p (q 0)) else 0 := by
  have hdiag : cavityFiniteCovariancePath rho lam hrho hsum g p q 0 =
      Matrix.diagonal (fun i =>
        (finiteInverse rho lam hrho hsum (deficit p (q 0)) - lam (g i))⁻¹) := by
    simpa only [cavityFiniteCovariancePath, cavityFiniteDeficitPath,
      cavityFiniteLevel_zero] using cavityFiniteCovariance_diagonal rho lam hrho hsum g hx
  unfold cavityFiniteRootCovariance
  rw [hdiag, Matrix.diagonal_mul_diagonal]
  simp only [cavityFiniteDeficitPath, cavityFiniteLevel_zero, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, ite_true, projectedResolventDerivative,
      hx, ite_true, div_eq_mul_inv, mul_inv_rev, pow_two]
    ring
  · simp [hij]

lemma cavity_finite_noise_weighted_entry (rho lam : Fin m → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) {n : ℕ} (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (q : Fin (n + 1) → ℝ)
    (hx : ∀ j, 0 < deficit p (q j)) (k : Fin n) (i j : Fin d) :
    rho (g i) * cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q k i j =
      if i = j then
        (projectedResolvent rho lam hrho hsum (g i) (deficit p (q k.castSucc)) -
          projectedResolvent rho lam hrho hsum (g i) (deficit p (q k.succ))) /
            cut k.castSucc.succ else 0 := by
  have hleft := cavity_finite_covariance_weighted_entry rho lam hrho hsum g
    (hx k.castSucc) i j
  have hright := cavity_finite_covariance_weighted_entry rho lam hrho hsum g
    (hx k.succ) i j
  simp only [cavityFiniteNoiseCovariance, cavityFiniteCovariancePath,
    cavityFiniteDeficitPath, cavityFiniteLevel_castSucc, cavityFiniteLevel_succ,
    chainExponent_apply cut k.isLt, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  calc
    _ = (cut k.castSucc.succ)⁻¹ *
        (rho (g i) * cavityFiniteCovariance rho lam hrho hsum g
          (deficit p (q k.castSucc)) i j -
        rho (g i) * cavityFiniteCovariance rho lam hrho hsum g
          (deficit p (q k.succ)) i j) := by
      change rho (g i) * ((cut k.castSucc.succ)⁻¹ *
        (cavityFiniteCovariance rho lam hrho hsum g (deficit p (q k.castSucc)) i j -
          cavityFiniteCovariance rho lam hrho hsum g (deficit p (q k.succ)) i j)) = _
      ring
    _ = _ := by
      rw [hleft, hright]
      by_cases hij : i = j <;> simp [hij, div_eq_mul_inv, mul_comm]

end InvariantIsing

end

end OAI
