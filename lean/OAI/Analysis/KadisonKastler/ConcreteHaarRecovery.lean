import OAI.Analysis.KadisonKastler.ConcreteHaarArc
import OAI.Analysis.KadisonKastler.HaarProjectionApproximation
import OAI.Analysis.KadisonKastler.HaarRecovery

namespace OAI

/-! # Scalar recovery from a free Haar unitary

The spectral arc, its trace, the two centered projection moments and the
tail identity are constructed from the actual unitary. The conclusion
uses the explicit continuous corner contraction, with no spectral
projection or freeness consequence left as an auxiliary premise.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The explicit Haar-polynomial contraction recovers at least one half of
the scalar, using only the free Haar moments and the finite-vector trace. -/
theorem concrete_haar_recovery_at_least_half
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ)
    (u : unitary (Algebra M)) {Base : StarSubalgebra ℂ (Algebra M)}
    (hfree : FreeHaarMoments τ Base u)
    {n N : ℕ} (hn : 0 < n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    (p : Algebra M) (hp : IsStarProjection p) (hpBase : p ∈ Base)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ)) :
    1 / 2 ≤ (τ.toLinearMap ((n : ℂ) •
      (unitaryHaarPolynomial N u * recoveryContraction n p (unitaryHaarPolynomial N u) *
        unitaryHaarPolynomial N u))).re := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hpower : (1 : ℝ) ≤ (100 * Real.pi) ^ 3 := one_le_pow₀ (by linarith)
  have hN100 : (100 : ℝ) ≤ N := by
    have hmul := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 100 * (n : ℝ) by positivity)
    nlinarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100) hN100
  let a : ℝ := 100 * Real.pi / N
  have ha : 0 < a := by dsimp [a]; positivity
  have hapi : a ≤ Real.pi := by
    dsimp [a]
    apply (div_le_iff₀ hNpos).2
    nlinarith [mul_le_mul_of_nonneg_right hN100 Real.pi_pos.le]
  have hmass : a / Real.pi = 100 / (N : ℝ) := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, ne_of_gt hNpos]
  obtain ⟨E⟩ := nonempty_haarArcProjection τ hτ u hfree.haar_moment a
  let A := haarLaurentTraceClosure τ u
  have huA : (u : Algebra M) ∈ A := unitary_mem_haarLaurentTraceClosure τ u
  have heA : E.projection ∈ A :=
    mem_haarLaurentTraceClosure_of_functional_limit τ u (unitaryCircleCFC u)
      (unitaryCircleCFC_fourier u) (haarArcCutoff a) E.projection E.two_limit
  have heτ : τ.toLinearMap E.projection = ((100 / (N : ℝ) : ℝ) : ℂ) := by
    simpa only [hmass] using E.trace hτ hfree.haar_moment ha.le hapi
  have hind : ProjectionTraceIndependent τ p A :=
    hfree.projectionTraceIndependent_haarLaurentTraceClosure hpBase
  have hmom : CenteredProjectionMoments τ p E.projection (n : ℝ)⁻¹ (100 / N) :=
    hfree.centeredProjectionMoments_of_functional_limit (unitaryCircleCFC u)
      (unitaryCircleCFC_fourier u) (haarArcCutoff a) hpBase hpτ heτ E.two_limit
  exact haar_recovery_at_least_half τ u hfree.haar_moment hn hsize huA p E.projection
    hp E.isStarProjection heA (E.polynomial_commute N) hpτ heτ hind hmom
    (E.tail hτ hfree.haar_moment ha.le hapi N)

/-- Complete scalar-recovery data for the actual corner contraction. -/
theorem concrete_haar_recovery
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ)
    (u : unitary (Algebra M)) {Base : StarSubalgebra ℂ (Algebra M)}
    (hfree : FreeHaarMoments τ Base u)
    {n N : ℕ} (hn : 0 < n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    (p : Algebra M) (hp : IsStarProjection p) (hpBase : p ∈ Base)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ)) :
    ‖recoveryContraction n p (unitaryHaarPolynomial N u)‖ ≤ 1 ∧
      p * recoveryContraction n p (unitaryHaarPolynomial N u) =
        recoveryContraction n p (unitaryHaarPolynomial N u) ∧
      recoveryContraction n p (unitaryHaarPolynomial N u) * p =
        recoveryContraction n p (unitaryHaarPolynomial N u) ∧
      1 / 2 ≤ (τ.toLinearMap ((n : ℂ) •
        (unitaryHaarPolynomial N u * recoveryContraction n p (unitaryHaarPolynomial N u) *
          unitaryHaarPolynomial N u))).re := by
  obtain ⟨hleft, hright⟩ := recoveryContraction_support hn p (unitaryHaarPolynomial N u) hp
  exact ⟨recoveryContraction_norm_le hn p (unitaryHaarPolynomial N u), hleft, hright,
    concrete_haar_recovery_at_least_half τ hτ u hfree hn hsize p hp hpBase hpτ⟩

end

end KadisonKastler

end OAI
