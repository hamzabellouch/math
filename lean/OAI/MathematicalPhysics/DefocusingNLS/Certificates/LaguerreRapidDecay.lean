import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreIteratedSlowGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreTail

namespace OAI

/-! # Rapid decay of the actual slow-solution Laguerre coefficients -/

open Filter Topology MeasureTheory Set Polynomial

namespace DefocusingNLS

theorem laguerreIteratedSlowJet_coefficient_succ (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (j n : ℕ) :
    laguerreCoefficientIntegral (laguerreIteratedSlowJet q m s (j + 1) 0) n =
      (n : ℂ) * laguerreCoefficientIntegral (laguerreIteratedSlowJet q m s j 0) n := by
  let d := laguerreIteratedSlowJet q m s j
  let p := laguerrePolynomial n
  have hi (k : ℕ) (r : ℂ[X]) : IntegrableOn (weightedPolynomialIntegrand (d k) r) (Ioi 0) :=
    integrableOn_weightedPolynomial_laguerreIteratedSlowJet q m s hq hsre hsim j k r
  have hg := weightedPolynomialIntegral_laguerre_operator (d 0) (d 1) (d 2) p
    (fun t _ => hasDerivAt_laguerreIteratedSlowJet q m s hq hsim j 0 t)
    (fun t _ => hasDerivAt_laguerreIteratedSlowJet q m s hq hsim j 1 t)
    (continuous_laguerreIteratedSlowJet q m s hq hsim j 0).continuousWithinAt
    (continuous_laguerreIteratedSlowJet q m s hq hsim j 1).continuousWithinAt
    (hi 0) (hi 1) (hi 2)
  have hp : laguerreOperator p = -C (n : ℂ) * p := laguerreOperator_laguerrePolynomial n
  rw [hp] at hg
  have he : weightedPolynomialIntegral (d 0) (-C (n : ℂ) * p) =
      -(n : ℂ) * weightedPolynomialIntegral (d 0) p := by
    change weightedPolynomialFunctional (d 0) (hi 0) _ = _
    rw [neg_mul, map_neg, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [weightedPolynomialFunctional_apply, neg_mul]
  rw [he] at hg
  have ho : laguerreCoefficientIntegral (laguerreIteratedSlowJet q m s (j + 1) 0) n =
      -(weightedPolynomialIntegral (d 2) (X * p) +
        weightedPolynomialIntegral (d 1) ((1 - X) * p)) := by
    unfold weightedPolynomialIntegral
    rw [← integral_add (hi 2 (X * p)) (hi 1 ((1 - X) * p)), ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (Real.exp (-t) : ℂ) * laguerreJetOperator d 0 t * p.eval (t : ℂ) = _
    simp only [laguerreJetOperator, Nat.cast_zero, zero_add, zero_mul, sub_zero,
      weightedPolynomialIntegrand, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one]
    ring
  rw [ho, hg]
  change -(-(n : ℂ) * weightedPolynomialIntegral (d 0) p) =
    (n : ℂ) * weightedPolynomialIntegral (d 0) p
  ring

theorem laguerreIteratedSlowJet_coefficient (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (j n : ℕ) :
    laguerreCoefficientIntegral (laguerreIteratedSlowJet q m s j 0) n =
      (n : ℂ) ^ j * slowLaguerreCoefficient q m s n := by
  induction j with
  | zero => simp [laguerreIteratedSlowJet, slowLaguerreCoefficient]
  | succ j ih =>
      rw [laguerreIteratedSlowJet_coefficient_succ q m s hq hsre hsim j n, ih, pow_succ]
      ring

/-- Every power of the coefficient index times the actual coefficient tends
to zero. Each integration by parts is justified by the proved jet bounds. -/
theorem slowLaguerreCoefficient_rapid_decay (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ j * slowLaguerreCoefficient q m s n)
      atTop (𝓝 0) := by
  have ht := laguerreCoefficientIntegral_tendsto_zero _
    (memLp_halfWeighted_laguerreIteratedSlowJet q m s hq hsre hsim j 0)
  convert! ht using 1
  funext n
  exact (laguerreIteratedSlowJet_coefficient q m s hq hsre hsim j n).symm

end DefocusingNLS

end OAI
