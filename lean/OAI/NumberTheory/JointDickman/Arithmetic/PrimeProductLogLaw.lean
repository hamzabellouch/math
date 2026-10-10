import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductIntervalLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-!
# Prime-product intervals in logarithmic coordinates

The logarithmic density is the exact change of variables in the harmonic
interval formula, not an independent smoothness assumption.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_integral (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    (hB : 0 < B) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, scaledRoughDensity c z H B s) =
      primeNormalizer (auxiliaryPrimes B) z *
        ∫ t in Real.exp (B * a)..Real.exp (B * b),
          roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let D := roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
  let f := fun s : ℝ => Real.exp (B * s)
  let f' := fun s : ℝ => (B : ℝ) * Real.exp (B * s)
  let g := fun t : ℝ => D (Real.log t) / t
  have hd : ∀ s ∈ Set.uIcc a b, HasDerivAt f (f' s) s := by
    intro s _
    convert ((hasDerivAt_id s).const_mul (B : ℝ)).exp using 1 <;> simp [f, f', mul_comm]
  have hc : ContinuousOn f' (Set.uIcc a b) := by dsimp [f']; fun_prop
  have hg : ContinuousOn g (f '' Set.uIcc a b) := by
    rintro t ⟨s, hs, rfl⟩
    rw [Set.uIcc_of_le hab] at hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hpos : 0 < f s := Real.exp_pos _
    have hlog : 0 < Real.log (f s) := by dsimp [f]; rw [Real.log_exp]; positivity
    exact (((roughDensityPolynomial_continuousAt c _ z H hlog).comp
      (Real.continuousAt_log hpos.ne')).div continuousAt_id hpos.ne').continuousWithinAt
  have hchange := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  calc
    _ = ∫ s in a..b, primeNormalizer (auxiliaryPrimes B) z * ((g ∘ f) s * f' s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have hs0 : 0 < s := ha.trans_le hs.1
      rw [scaledRoughDensity_eq c z H B hB hs0]
      dsimp [g, f, f', D]
      rw [Real.log_exp]
      field_simp
    _ = primeNormalizer (auxiliaryPrimes B) z * ∫ s in a..b, (g ∘ f) s * f' s :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [hchange]

/-- The actual prime-product probability of a log-coordinate interval. -/
theorem primeProduct_log_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        0 < a → a ≤ b → b ≤ 4 →
        9 ≤ Real.exp (B * a) → (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a →
        |(∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
            primeProductMass (auxiliaryPrimes B) z n) -
          ∫ s in a..b, scaledRoughDensity c z H B s| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) + K * (B : ℝ) ^ (-D) * (2 + B * (b - a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_interval_law hSD hM hz D
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hsize hscale
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hexp : Real.exp (B * a) ≤ Real.exp (B * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hupper : Real.exp (B * b) ≤ auxiliaryUpper B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := hB (Real.exp (B * a)) (Real.exp (B * b)) hsize hexp hupper
    (by simpa only [Real.log_exp] using hscale)
  rw [← scaledRoughDensity_integral c z H B hB0 ha hab] at h
  have hlog : Real.log (Real.exp (B * b) / Real.exp (B * a)) = B * (b - a) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  simpa only [hlog] using h

end JointDickman

end OAI
