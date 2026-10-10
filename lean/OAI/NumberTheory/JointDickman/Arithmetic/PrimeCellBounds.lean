import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteLocalLaw
import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityRegularity

namespace OAI

/-! # Uniform interval upper bounds for the actual prime-site law -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_integral_le (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbound : ∀ s ∈ Set.Icc a b, scaledRoughDensity c z H B s ≤ M) :
    (∫ s in a..b, scaledRoughDensity c z H B s) ≤ M * (b - a) := by
  have hc : ContinuousOn (scaledRoughDensity c z H B) (Set.Icc a b) := by
    intro s hs
    exact (hasDerivAt_scaledRoughDensity c z H B (ha.trans_le hs.1)).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (scaledRoughDensity c z H B) MeasureTheory.volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

open Classical in
/-- The absolute local-law error is retained, so arbitrarily short cells
are included. The two exponents are exactly those needed downstream. -/
theorem primeSite_interval_upper
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 1 / 4 ≤ a → a ≤ b → b ≤ 16 / 5 →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ r : (ZMod q)ˣ,
      (∑ x : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
          bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) ≤
        M * (b - a) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc, _, H, C, hC, hlocal⟩ := primeSite_local_law hSD hSW hM hz
  have hzpos : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨M, hMpos, L, hbounded⟩ := scaledRoughDensity_bounded_lipschitz
    hM hMP c hc hzpos hzhalf (by norm_num : (0 : ℝ) < 1 / 4) H
  have hsmall : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 4 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      (fun _ h => h.le)
  refine ⟨M, C, hMpos, hC, ?_⟩
  filter_upwards [hlocal, hbounded, hsmall] with B hlocalB hboundedB hsmallB
  intro a b ha hab hb q _ hq r
  have he := hlocalB a b (hsmallB.trans ha) hab hb q hq r
  have hi := scaledRoughDensity_integral_le c z H B (by linarith : 0 < a) hab
    (fun s hs => (le_abs_self _).trans (hboundedB.1 s (ha.trans hs.1)))
  have hφ : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hi' := div_le_div_of_nonneg_right hi hφ
  have he' := (abs_le.mp he).2
  linarith

end JointDickman

end OAI
