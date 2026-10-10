import OAI.NumberTheory.Ostmann.Quadratic.QuadraticInverseRanges

namespace OAI

/-! # A witness gives the denominator and accuracy at the manuscript scales -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem quadratic_progression_scale_range (T R c : ℝ) (hT : 0 ≤ T) (hc : 1 ≤ c)
    (hcupper : c ≤ Real.exp (3 * T / 25))
    (hRlo : Real.exp (10 * T) ≤ R) (hRhi : R ≤ Real.exp (14 * T)) :
    Real.exp (4 * T) ≤ Real.sqrt (R / c) ∧
      Real.sqrt (R / c) ≤ Real.exp (7 * T) := by
  have hcpos : 0 < c := by linarith
  have hRpos : 0 < R := (Real.exp_pos _).trans_le hRlo
  constructor
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hcpos).mpr
    rw [← Real.exp_nat_mul]
    calc
      _ ≤ Real.exp (8 * T) * Real.exp (3 * T / 25) := by
        simp only [Nat.cast_ofNat]
        rw [show 2 * (4 * T) = 8 * T by ring]
        exact mul_le_mul_of_nonneg_left hcupper (Real.exp_nonneg (8 * T))
      _ = Real.exp (8 * T + 3 * T / 25) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (10 * T) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ R := hRlo
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_nat_mul]
    apply (div_le_iff₀ hcpos).mpr
    have hh := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg (14 * T))
    norm_num only [Nat.cast_ofNat] at *
    have he : 2 * (7 * T) = 14 * T := by ring
    rw [he]
    nlinarith

/-- The original weighted series, with the original residue argument and
the original scale R, yields a rational approximation. All numerical
inequalities needed by the inverse theorem have been discharged. -/
theorem eventual_positiveQuadraticSum_phase_witness (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (q s v : ℕ) [NeZero q] (g : ZMod q → ℂ)
      (a : ZMod q) (h₀ : ℕ) (θ R K : ℝ),
      (∀ x, ¬IsUnit x → g x = 0) → (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q →
      0 < s → 0 < v → 0 ≤ K → K ≤ T ^ (9999999 / 10000000 : ℝ) →
      ((s * v * q : ℕ) : ℝ) ≤ Real.exp (3 * T / 25) →
      Real.exp (10 * T) ≤ R → R ≤ Real.exp (14 * T) →
      Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
        ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖ →
      ∃ c ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ b : ℤ,
        |(c : ℝ) * θ - b| ≤ Real.exp (13 * T / 100) / R := by
  let J := 4 * quadraticVariationBudget Φ B * (B + 1)
  have hJ : 1 ≤ J := by
    have hD := quadraticVariationBudget_one_le Φ B hB
    dsimp [J]
    nlinarith
  filter_upwards [eventual_quadratic_inverse_factor B J hB hJ,
    eventually_ge_atTop (1 : ℝ)] with T hfactor hT
  intro q s v _ g a h₀ θ R K hg henergy hs hv hK hKT hcupper hRlo hRhi hlarge
  let c : ℝ := ((s * v * q : ℕ) : ℝ)
  have hc : 1 ≤ c := by
    have hp : 0 < s * v * q := Nat.mul_pos (Nat.mul_pos hs hv) (NeZero.pos q)
    dsimp [c]
    exact_mod_cast (show 1 ≤ s * v * q from hp)
  have hR : 0 < R := (Real.exp_pos _).trans_le hRlo
  have hec : c = (s : ℝ) * v * q := by dsimp [c]; push_cast; rfl
  have hyrange := quadratic_progression_scale_range T R c (by linarith) hc hcupper hRlo hRhi
  have hysq : (Real.sqrt (R / c)) ^ 2 = R / c := Real.sq_sqrt (by positivity)
  have hnum := quadratic_inverse_ranges T K B J (Real.sqrt (R / c)) R c hT hK hB hJ
    hyrange.1 hR (by linarith) hcupper hysq (hfactor K _ hKT hyrange.1 hyrange.2)
  obtain ⟨hscale, hdenom, herr⟩ := hnum
  have hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)) := by
    rw [← hec]
    exact (Real.one_le_exp_iff.mpr (by linarith)).trans hyrange.1
  obtain ⟨c₀, hc₀, b, hb⟩ := positiveQuadraticSum_phase_witness g hg henergy a h₀ s v
    ⌈Real.exp (13 * T / 100)⌉₊ θ R B K Φ hs hv hR hB hK hY hΦ hlarge
    (by simpa only [J, hec] using hscale)
    (hdenom.trans (Nat.le_ceil _))
  refine ⟨c₀, hc₀, b, hb.trans ?_⟩
  simpa only [J, hec] using herr

end Ostmann

end OAI
