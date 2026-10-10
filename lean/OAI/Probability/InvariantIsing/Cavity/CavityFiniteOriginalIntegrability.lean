import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariancePath
import OAI.Probability.InvariantIsing.Cavity.CavityRootedReplicaTransport

namespace OAI

/-! Full exponential integrability at the actual finite spectral
covariances, with the Gaussian precision conditions discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_original_integrability {m d N n k : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    ∀ᵐ ω ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
        (cavityGaussianMarks S) : Measure _),
      Integrable (fun z => Real.exp (cavityLogFactor K L C (cavityRootedField n z.1) z.2))
        ((cavityRootedPriorKernel n (H n) ω).prod π) := by
  intro K H S S₀
  have hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
  let x := cavityFiniteDeficitPath p q
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hxm : Antitone x := cavityFiniteDeficitPath_antitone p q hq.monotone
  have hK : K.transpose = K := by
    dsimp only [K, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hH (i : ℕ) : (H i).transpose = H i :=
    cavityFiniteCovariancePath_symmetric rho lam hrho hsum g p q i
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop i
  have hS₀ : S₀.PosSemidef :=
    cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g (hx 0) (hq0 0)
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_finite_tilt_isUnit rho lam hrho hsum B hB g (x i) (hx i)
  have hΔ (i : ℕ) : H i - H (i + 1) = chainExponent cut i • S i :=
    cavityFiniteNoiseCovariance_delta rho lam hrho hsum g p cut hcut hfirst q i
  have hA := cavity_finite_spectral_upper lam a ha B hB
  have hQ (i : ℕ) : (cavityFactorPrecision
      (chainExponent cut i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef :=
    cavityFiniteCovariance_step_precision rho lam hrho hsum g _ a hK hA
      (hx (i + 1)) (hxm (Nat.le_succ i)) (finite_chainExponent_pos cut hcut hfirst i).le
      (S i) (hS i) (hΔ i)
  have hR : (H n).PosSemidef :=
    (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast q hq hp htop n).posSemidef
  have hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef :=
    cavityFiniteCovariance_terminal_precision rho lam hrho hsum g _ a (fun i => ha (g i)) hK hA (hx n)
  exact (cavity_rooted_full_integrability n K H S (chainExponent cut) S₀ hS₀ L C
    (chainExponent_admissible hcut hfirst hlast) hK hH hS
    (finite_chainExponent_pos cut hcut hfirst) hdet hΔ hQ hR hQR π).mono (fun _ h => h.2)

end InvariantIsing

end

end OAI
