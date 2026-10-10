import OAI.MathematicalPhysics.DefocusingNLS.Certificates.NormalizedForwardJet

namespace OAI

/-! # Positive forward cone growth to the right of the counting region -/

namespace DefocusingNLS

theorem normalizedForwardJet_cone_monotone (M : ℝ) (s q : ℂ) (w : Fin 2 → ℂ)
    (hs : s.re = 0) (hq : M / 2 ≤ q.re)
    (hd : ∀ n : ℕ, q + n - (M : ℂ) ≠ 0) :
    Monotone (fun n => coneForm M s (normalizedForwardJet M s q w n 0)
      (normalizedForwardJet M s q w n 1)) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := normalizedForwardJet_increment M s q w n hs (hd n)
  have hnonneg : 0 ≤ ((q + n).re - M / 2) * Complex.normSq
      (normalizedForwardJet M s q w n 0 - normalizedForwardJet M s q w (n + 1) 0) := by
    apply mul_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

theorem normalizedForwardJet_first_strict (M : ℝ) (s q : ℂ) (w : Fin 2 → ℂ)
    (hs : s.re = 0) (hq : M / 2 < q.re) (hd : q - (M : ℂ) ≠ 0)
    (hs0 : s ≠ 0) (hw0 : w 0 = 0) (hw1 : w 1 ≠ 0) :
    coneForm M s (w 0) (w 1) <
      coneForm M s (normalizedForwardJet M s q w 1 0)
        (normalizedForwardJet M s q w 1 1) := by
  have hfirst : normalizedForwardJet M s q w 1 0 ≠ 0 := by
    rw [normalizedForwardJet_succ_first _ _ _ _ 0]
    simpa [normalizedForwardJet, hw0] using div_ne_zero (mul_ne_zero hs0 hw1) hd
  have h := normalizedForwardJet_increment M s q w 0 hs (by simpa using hd)
  simp only [Nat.cast_zero, add_zero] at h
  change coneForm M s (normalizedForwardJet M s q w 1 0)
      (normalizedForwardJet M s q w 1 1) - coneForm M s (w 0) (w 1) =
      (q.re - M / 2) * Complex.normSq (w 0 - normalizedForwardJet M s q w 1 0) at h
  rw [hw0, zero_sub, Complex.normSq_neg] at h
  rw [hw0]

  have hp := mul_pos (sub_pos.mpr hq) (Complex.normSq_pos.mpr hfirst)
  linarith

/-- Opposite initial cross terms cancel. Strict growth in one channel covers
initial vectors whose first coordinate vanishes. -/
theorem normalizedForwardJet_sum_cone_pos (M : ℝ) (s q₁ q₂ : ℂ)
    (w : Fin 2 → ℂ) (N : ℕ) (hM : 0 < M) (hs : s.re = 0) (hs0 : s ≠ 0)
    (hq₁ : M / 2 < q₁.re) (hq₂ : M / 2 < q₂.re)
    (hd₁ : ∀ n : ℕ, q₁ + n - (M : ℂ) ≠ 0)
    (hd₂ : ∀ n : ℕ, q₂ + n - (M : ℂ) ≠ 0) (hN : 1 ≤ N) (hw : w ≠ 0) :
    0 < coneForm M s (normalizedForwardJet M s q₁ w N 0)
        (normalizedForwardJet M s q₁ w N 1) +
      coneForm M (-s) (normalizedForwardJet M (-s) q₂ w N 0)
        (normalizedForwardJet M (-s) q₂ w N 1) := by
  have hm₁ := normalizedForwardJet_cone_monotone M s q₁ w hs hq₁.le hd₁
  have hm₂ := normalizedForwardJet_cone_monotone M (-s) q₂ w (by simpa using hs) hq₂.le hd₂
  have hsum : coneForm M s (w 0) (w 1) + coneForm M (-s) (w 0) (w 1) =
      M * Complex.normSq (w 0) := by
    simp [coneForm]
    ring
  have h₂ := hm₂ (Nat.zero_le N)
  change coneForm M (-s) (w 0) (w 1) ≤ _ at h₂
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := by
      intro hz
      apply hw
      funext i
      fin_cases i <;> simp [hw0, hz]
    have hstrict := normalizedForwardJet_first_strict M s q₁ w hs hq₁
      (by simpa using hd₁ 0) hs0 hw0 hw1
    have h₁ := hm₁ hN
    rw [hw0, Complex.normSq_zero, mul_zero] at hsum
    rw [hw0] at hstrict h₂
    linarith
  · have h₁ := hm₁ (Nat.zero_le N)
    change coneForm M s (w 0) (w 1) ≤ _ at h₁
    have hp := mul_pos hM (Complex.normSq_pos.mpr hw0)
    linarith

end DefocusingNLS

end OAI
