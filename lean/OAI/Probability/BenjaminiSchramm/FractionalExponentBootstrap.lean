import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section

namespace Percolation.BenjaminiSchramm

theorem fractional_exponent_bootstrap (D U : ℝ → Prop) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hD0 : D 0)
    (hup : ∀ q : ℝ, 0 ≤ q → q < 1 → D q → ∀ q' : ℝ,
      0 < q' → q' < q+η*(1-q) → U q')
    (hdown : ∀ q : ℝ, 0 < q → q < 1 → U q → ∀ q' : ℝ,
      0 ≤ q' → q' < q → D q') :
    ∀ q : ℝ, 0 < q → q < 1 → D q ∧ U q := by
  have hstep (q q' : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hDq : D q)
      (hq'0 : 0 ≤ q') (hq' : q' < q+η*(1-q)) : D q' := by
    let u := (q'+(q+η*(1-q)))/2
    have hupper : q+η*(1-q) < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hη1) (sub_pos.mpr hq1)]
    have hu0 : 0 < u := by dsimp [u]; linarith
    have hu1 : u < 1 := by dsimp [u]; linarith
    have hulim : u < q+η*(1-q) := by dsimp [u]; linarith
    have hqu : q' < u := by dsimp [u]; linarith
    exact hdown u hu0 hu1 (hup q hq0 hq1 hDq u hu0 hulim) q' hq'0 hqu
  let r := 1-η/2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let s (n : ℕ) := 1-r^n
  have hs0 (n : ℕ) : 0 ≤ s n := sub_nonneg.mpr (pow_le_one₀ hr0.le hr1.le)
  have hs1 (n : ℕ) : s n < 1 := by dsimp [s]; linarith [pow_pos hr0 n]
  have hDs : ∀ n : ℕ, D (s n) := by
    intro n
    induction n with
    | zero => simpa only [s,pow_zero,sub_self] using hD0
    | succ n ih =>
      apply hstep (s n) (s (n+1)) (hs0 n) (hs1 n) ih (hs0 (n+1))
      have hpow := pow_pos hr0 n
      have hproduct := mul_pos hη hpow
      dsimp [s]
      rw [pow_succ]
      dsimp [r] at hproduct ⊢
      nlinarith
  intro q hq0 hq1
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hq1) hr1
  have hqs : q < s n := by dsimp [s]; linarith
  have hUs : U (s n) := by
    have hsn0 : 0 < s n := hq0.trans hqs
    exact hup (s n) (hs0 n) (hs1 n) (hDs n) (s n) hsn0
      (lt_add_of_pos_right _ (mul_pos hη (sub_pos.mpr (hs1 n))))
  have hDq : D q := hdown (s n) (hq0.trans hqs) (hs1 n) hUs q hq0.le hqs
  exact ⟨hDq,hup q hq0.le hq1 hDq q hq0
    (lt_add_of_pos_right _ (mul_pos hη (sub_pos.mpr hq1)))⟩

end Percolation.BenjaminiSchramm

end

end OAI
