import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteDeficitPath
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianMarkDepth

namespace OAI

/-! The actual finite cascade covariance path and independent Gaussian
increments, including zero increments beyond the terminal level. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder BigOperators

namespace InvariantIsing

variable {m d n : ℕ}

def cavityFiniteCovariancePath (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (i : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  cavityFiniteCovariance rho lam hrho hsum g (cavityFiniteDeficitPath p q i)

def cavityFiniteNoiseCovariance (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (q : Fin (n + 1) → ℝ)
    (i : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (chainExponent cut i)⁻¹ • (cavityFiniteCovariancePath rho lam hrho hsum g p q i -
    cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1))

def cavityFiniteRootCovariance (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → Fin m)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  q 0 • ((1 / finiteSecondResolvent rho lam
    (finiteInverse rho lam hrho hsum (cavityFiniteDeficitPath p q 0))) •
      (cavityFiniteCovariancePath rho lam hrho hsum g p q 0 *
        cavityFiniteCovariancePath rho lam hrho hsum g p q 0))

variable (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
  (g : Fin d → Fin m) (p : OverlapPath) (cut : Fin (n + 2) → ℝ)
  (hcut : StrictMono cut) (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
  (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
  (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
  (htop : q (Fin.last n) < 1)

include hfirst hlast hq hp htop in
lemma cavityFiniteCovariancePath_posDef (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).PosDef :=
  cavityFiniteCovariance_posDef rho lam hrho hsum g
    (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i)

lemma cavityFiniteCovariancePath_symmetric (i : ℕ) :
    (cavityFiniteCovariancePath rho lam hrho hsum g p q i).transpose =
      cavityFiniteCovariancePath rho lam hrho hsum g p q i := by
  simp only [cavityFiniteCovariancePath, cavityFiniteCovariance,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.diagonal_transpose]

include hcut hfirst in
lemma cavityFiniteNoiseCovariance_delta (i : ℕ) :
    cavityFiniteCovariancePath rho lam hrho hsum g p q i -
      cavityFiniteCovariancePath rho lam hrho hsum g p q (i + 1) =
        chainExponent cut i • cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i := by
  rw [cavityFiniteNoiseCovariance, smul_smul,
    mul_inv_cancel₀ (finite_chainExponent_pos cut hcut hfirst i).ne', one_smul]

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posSemidef (i : ℕ) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact cavityFiniteCovariance_sub_posSemidef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_antitone p q hq.monotone (Nat.le_succ i))
  · exact inv_nonneg.mpr (finite_chainExponent_pos cut hcut hfirst i).le

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_posDef (i : Fin n) :
    (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i).PosDef := by
  apply Matrix.PosDef.smul
  · exact cavityFiniteCovariance_sub_posDef rho lam hrho hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop (i + 1))
      (cavityFiniteDeficitPath_step_strict p cut hcut hfirst hlast q hq hp i)
  · exact inv_pos.mpr (finite_chainExponent_pos cut hcut hfirst i)

include hcut hfirst hlast hq hp htop in
lemma cavityFiniteNoiseCovariance_atomless (hd : 0 < d) (i : ℕ) (hi : i < n) :
    NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      (cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q i)) := by
  have hs := cavityFiniteNoiseCovariance_posDef rho lam hrho hsum g p cut hcut hfirst hlast
    q hq hp htop ⟨i, hi⟩
  exact cavity_multivariateGaussian_nullSingleton _ hs.posSemidef ⟨0, hd⟩ hs.diag_pos

end InvariantIsing

end

end OAI
