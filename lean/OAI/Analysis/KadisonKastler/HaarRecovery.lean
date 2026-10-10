import OAI.Analysis.KadisonKastler.ConcreteScalarRecovery
import OAI.Analysis.KadisonKastler.SpectralRecovery
import OAI.Analysis.KadisonKastler.FreeHaarClosure

namespace OAI

/-! # Scalar recovery from the actual Haar polynomial

The scalar trace formula for the arc projection combines with the
geometric-sum tail, tracial normalization, and compression estimates
to recover scalar coefficients.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The actual polynomial and the constructed corner contraction recover
at least one half of the identity's scalar coefficient. -/
theorem haar_recovery_at_least_half
    (τ : FaithfulTracialState (Algebra M)) (u : unitary (Algebra M))
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0)
    {n N : ℕ} (hn : 0 < n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    {A : StarSubalgebra ℂ (Algebra M)} (huA : (u : Algebra M) ∈ A)
    (p e : Algebra M) (hp : IsStarProjection p) (he : IsStarProjection e)
    (heA : e ∈ A)
    (hcomm : Commute (unitaryHaarPolynomial N u) e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = ((100 / (N : ℝ) : ℝ) : ℂ))
    (hind : ProjectionTraceIndependent τ p A)
    (hmom : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ (100 / N))
    (hspectral : (τ.toLinearMap
      (star (unitaryHaarPolynomial N u) * unitaryHaarPolynomial N u * (1 - e))).re =
        haarTailEnergy N (100 * Real.pi / N)) :
    1 / 2 ≤ (τ.toLinearMap ((n : ℂ) •
      (unitaryHaarPolynomial N u * recoveryContraction n p (unitaryHaarPolynomial N u) *
        unitaryHaarPolynomial N u))).re := by
  have hN : 0 < N := by
    have hpositive : 0 < 100 * (n : ℝ) * (100 * Real.pi) ^ 3 := by positivity
    exact_mod_cast (lt_of_lt_of_le hpositive hsize)
  have hfA := unitaryHaarPolynomial_mem huA N
  have htail : (τ.toLinearMap
      (star (unitaryHaarPolynomial N u) * unitaryHaarPolynomial N u * (1 - e))).re ≤
        Real.pi / (100 * Real.pi) := by
    rw [hspectral]
    exact haarTailEnergy_div_le hN (by positivity)
  apply concrete_recovery_scalar_at_least_half M τ hn hsize p (unitaryHaarPolynomial N u) e
    hp he hpτ heτ hmom (norm_unitaryHaarPolynomial_mul_self_le u hN)
  · exact (compressed_spectral_tail_le τ hn hp he hfA heA hcomm hpτ hind).trans htail
  · exact normal_compressed_square_mass_lower τ (isStarNormal_unitaryHaarPolynomial N u)
      he hcomm (trace_unitaryHaarPolynomial_square τ u hhaar hN) htail

end

end KadisonKastler

end OAI
