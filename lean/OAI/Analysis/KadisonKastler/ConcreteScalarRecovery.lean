import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.ScalarRecovery
import OAI.Analysis.KadisonKastler.TraceCompressionPolar
import OAI.Analysis.FactorGeneration.Supports

namespace OAI

/-! # Actual polar decomposition in the concrete scalar-recovery argument -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)

local instance concreteRecoveryOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance concreteRecoveryStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Concrete polar decomposition supplies the support data required by
the tracial compression identity. -/
theorem exists_left_polar_with_support (x : Algebra M) :
    ∃ w : Algebra M,
      x = CFC.sqrt (x * star x) * w ∧ IsStarProjection (w * star w) ∧
      (w * star w) * CFC.sqrt (x * star x) = CFC.sqrt (x * star x) ∧
      CFC.sqrt (x * star x) * (w * star w) = CFC.sqrt (x * star x) := by
  obtain ⟨v, hv, hi, _⟩ := Generator.Tracial.exists_polar_decomposition (star x)
  simp only [star_star] at hv hi
  have hb : star (CFC.sqrt (x * star x)) = CFC.sqrt (x * star x) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  refine ⟨star v, ?_, ?_, ?_, ?_⟩
  · have hh := congrArg star hv
    simpa only [star_mul, hb, star_star] using hh.symm
  · simpa only [star_star, hi] using (Generator.Tracial.rangeProjection (CFC.sqrt (x * star x))).property
  · simpa only [star_star, hi] using Generator.Tracial.rangeProjection_mul (CFC.sqrt (x * star x))
  · have ht := congrArg star (Generator.Tracial.rangeProjection_mul (CFC.sqrt (x * star x)))
    simpa only [star_mul, hb, (Generator.Tracial.rangeProjection (CFC.sqrt (x * star x))).property.isSelfAdjoint.star_eq,
      star_star, hi] using ht

/-- Polar decomposition gives the projection-compression identity for
concrete von Neumann algebras. -/
theorem concrete_traceOneNorm_scaled_projection_compression
    (τ : FaithfulTracialState (Algebra M)) (n : ℕ) (p e a : Algebra M)
    (hp : IsStarProjection p) (he : IsStarProjection e) :
    (n : ℝ) * traceOneNorm τ (p * e * a * e * p) =
      traceOneNorm τ (CFC.sqrt ((n : ℂ) • (e * p * e)) * a *
        CFC.sqrt ((n : ℂ) • (e * p * e))) := by
  obtain ⟨w, hx, hw, hL, hR⟩ := exists_left_polar_with_support M
    ((Real.sqrt (n : ℝ)) • (e * p))
  rw [scaled_projection_product_mul_star n p e hp he] at hx hL hR
  exact traceOneNorm_scaled_projection_compression τ n p e a w hp he hx hw hL hR

/-- Two spectral tail estimates bound the real part of the recovered
scalar below by one half. -/
theorem concrete_recovery_scalar_at_least_half
    (τ : FaithfulTracialState (Algebra M)) {n N : ℕ} (hn : 0 < n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    (p f e : Algebra M) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = ((100 / (N : ℝ) : ℝ) : ℂ))
    (hmom : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ (100 / N))
    (hf : ‖f * f‖ ≤ N)
    (htail : (n : ℝ) * traceOneNorm τ
      (recoveryCompression p f - p * e * (f * f) * e * p) ≤
        Real.pi / (100 * Real.pi))
    (hmass : 1 - Real.pi / (100 * Real.pi) ≤ traceOneNorm τ (e * (f * f) * e)) :
    1 / 2 ≤ (τ.toLinearMap ((n : ℂ) • (f * recoveryContraction n p f * f))).re := by
  exact recovery_scalar_at_least_half τ hn hsize p f e hp he hpτ heτ hmom hf htail hmass
    (concrete_traceOneNorm_scaled_projection_compression M τ n p e (f * f) hp he)

end

end KadisonKastler

end OAI
