import OAI.NumberTheory.Ostmann.Construction.LogWindowDiameter

namespace OAI

/-! # The multiplicative sieve on the actual support of a logarithmic window -/

namespace Ostmann

open scoped BigOperators Classical

 theorem localized_multiplicative_sieve (N Q : ℕ) (hQ : 1 ≤ Q)
    (x h : ℝ) (hh : 0 < h) (W : ℝ → ℂ)
    (hW : ∀ y, 1 ≤ |y| → W y = 0) (a : ℕ → ℂ)
    (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ Finset.Icc 1 N, a n * W ((x - Real.log n) / h) * χ (n : ZMod q)‖ ^ 2) ≤
        (2 * N * h + (Q : ℝ) ^ 2 + 2) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n * W ((x - Real.log n) / h)‖ ^ 2 := by
  let S : Finset ℕ := (Finset.Icc 1 N).filter fun n : ℕ => W ((x - Real.log n) / h) ≠ 0
  have hS (n : ℕ) (hn : n ∈ S) :
      1 ≤ n ∧ n ≤ N ∧ |Real.log n - x| ≤ h := by
    obtain ⟨hnN, hne⟩ := Finset.mem_filter.mp hn
    have hw : |(x - Real.log n) / h| < 1 := lt_of_not_ge (fun hy => hne (hW _ hy))
    have hh' : |x - Real.log n| < h := by
      rw [abs_div, abs_of_pos hh, div_lt_one hh] at hw
      exact hw
    exact ⟨(Finset.mem_Icc.mp hnN).1, (Finset.mem_Icc.mp hnN).2,
      by rw [abs_sub_comm]; exact hh'.le⟩
  obtain ⟨J, hJ⟩ := log_window_integer_interval S N x h hh.le hS
  have hs := finite_support_multiplicative_sieve S J (⌈2 * N * h⌉₊ + 1) Q
    (by omega) hQ hJ (fun n => a n * W ((x - Real.log n) / h)) F hF
  have hsum {A : Type} [AddCommMonoid A] (g : ℕ → A)
      (hg : ∀ n ∈ Finset.Icc 1 N, W ((x - Real.log n) / h) = 0 → g n = 0) :
      (∑ n ∈ S, g n) = ∑ n ∈ Finset.Icc 1 N, g n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    apply hg n hn
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
  have hpoly (q : ℕ) (χ : DirichletCharacter ℂ q) := hsum (A := ℂ)
    (fun n => a n * W ((x - Real.log n) / h) * χ (n : ZMod q))
    (by intro n _ hn; simp only [hn, mul_zero, zero_mul])
  have henergy := hsum (A := ℝ) (fun n => ‖a n * W ((x - Real.log n) / h)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simp_rw [hpoly] at hs
  rw [henergy] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (N : ℝ) * h)
  push_cast
  linarith

end Ostmann

end OAI
