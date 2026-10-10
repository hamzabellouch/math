import OAI.NumberTheory.Ostmann.QuadraticSieveDualReindexLattice

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem oddSquarefree_le_abs_signed_square (a : ℤ) (ha : a ≠ 0)
    (b : OddSquarefreeIndex) (c : {c : ℕ // 0 < c}) :
    (b.val : ℝ) ≤ |((a * (b.val : ℤ) * (c.val : ℤ) ^ 2 : ℤ) : ℝ)| := by
  have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hc1 : (1 : ℝ) ≤ c.val := by exact_mod_cast c.property
  have hc2 : (1 : ℝ) ≤ (c.val : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) ≤ b.val := Nat.cast_nonneg _
  have hab : (b.val : ℝ) ≤ |(a : ℝ)| * b.val := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hb0
  have htot : |(a : ℝ)| * b.val ≤ |(a : ℝ)| * b.val * (c.val : ℝ) ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 (mul_nonneg (abs_nonneg _) hb0)
  convert hab.trans htot using 1
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, abs_mul, abs_pow,
    abs_of_nonneg hb0, abs_of_nonneg (Nat.cast_nonneg c.val : (0 : ℝ) ≤ c.val)]

noncomputable def dualSquarefreeTail (W : 𝓢(ℝ, ℂ)) (a : ℤ) (e M : ℝ)
    (q : ℕ) (K : ℝ) : ℂ :=
  ∑' b : OddSquarefreeIndex, if K < (b.val : ℝ) then
    (jacobiSym (a * (b.val : ℤ)) q : ℂ) * dualSquareSum W (a : ℝ) e M (b.val : ℝ) q else 0

theorem dualSquarefreeTail_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ) (e M : ℝ) (q : ℕ) (K : ℝ),
      a ≠ 0 → 0 < e → 0 < M → 0 < q → 0 < K →
      ‖dualSquarefreeTail W a e M q K‖ ≤
        C / ((M / (e * q)) ^ (A + 2) * K ^ A) := by
  obtain ⟨C, hC, hbound⟩ := schwartz_injective_weighted_lattice_bound
    (ι := OddSquarefreeIndex × {c : ℕ // 0 < c}) (𝓕 W) A
  refine ⟨C, hC, ?_⟩
  intro a e M q K ha he hM hq hK
  let : NeZero q := ⟨hq.ne'⟩
  let ν : OddSquarefreeIndex × {c : ℕ // 0 < c} → ℤ :=
    fun p => a * (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2
  let F : OddSquarefreeIndex × {c : ℕ // 0 < c} → ℂ := fun p =>
    (jacobiSym (ν p) q : ℂ) * 𝓕 W ((ν p : ℝ) * M / (e * q))
  let w : OddSquarefreeIndex × {c : ℕ // 0 < c} → ℂ := fun p =>
    if K < (p.1.val : ℝ) then (jacobiSym (ν p) q : ℂ) else 0
  have hsum : Summable F := summable_dual_jacobi_pairs W a e M q ha he hM hq
  have hmasked : Summable (fun p => if K < (p.1.val : ℝ) then F p else 0) :=
    (hsum.indicator {p | K < (p.1.val : ℝ)}).congr (fun p => by simp [Set.indicator_apply])
  have heq : dualSquarefreeTail W a e M q K =
      ∑' p, w p * 𝓕 W ((ν p : ℝ) * (M / (e * q))) := by
    calc
      _ = ∑' b : OddSquarefreeIndex, ∑' c : {c : ℕ // 0 < c},
          if K < (b.val : ℝ) then F (b, c) else 0 := by
        unfold dualSquarefreeTail
        apply tsum_congr
        intro b
        by_cases hb : K < (b.val : ℝ)
        · simp only [ite_eq_left hb]
          exact (tsum_signed_jacobi_square_eq_dualSquareSum W a e M b.val q).symm
        · simp only [ite_eq_right hb, tsum_zero]
      _ = ∑' p, if K < (p.1.val : ℝ) then F p else 0 := hmasked.tsum_prod.symm
      _ = _ := by
        apply tsum_congr
        intro p
        by_cases hp : K < (p.1.val : ℝ) <;> simp [w, F, hp, mul_div_assoc]
  have hw : ∀ p, ‖w p‖ ≤ 1 := by
    intro p
    by_cases hp : K < (p.1.val : ℝ)
    · rcases jacobiSym.trichotomy (ν p) q with hj | hj | hj <;> simp [w, hp, hj]
    · simp [w, hp]
  have hcut : ∀ p, w p ≠ 0 → K ≤ |(ν p : ℝ)| := by
    intro p hp
    have hb : K < (p.1.val : ℝ) := by
      by_contra hn
      exact hp (by simp [w, hn])
    exact hb.le.trans (oddSquarefree_le_abs_signed_square a ha p.1 p.2)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [heq]
  exact hbound ν (signed_squarefree_pair_injective ha) w hw
    (M / (e * q)) K (by positivity) hK hcut

theorem signed_dualSquarefree_tail_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M : ℝ) (q : ℕ) (K : ℝ),
      0 < e → 0 < M → 0 < q → 0 < K →
      ‖∑ a ∈ signedSquarefreeMultipliers, dualSquarefreeTail W a e M q K‖ ≤
        C / ((M / (e * q)) ^ (A + 2) * K ^ A) := by
  obtain ⟨C, hC, hb⟩ := dualSquarefreeTail_bound W A
  refine ⟨4 * C, by positivity, ?_⟩
  intro e M q K he hM hq hK
  calc
    _ ≤ ∑ a ∈ signedSquarefreeMultipliers, ‖dualSquarefreeTail W a e M q K‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ signedSquarefreeMultipliers, C / ((M / (e * q)) ^ (A + 2) * K ^ A) :=
      Finset.sum_le_sum (fun a ha => hb a e M q K (signedSquarefreeMultiplier_ne_zero ha) he hM hq hK)
    _ = _ := by rw [Finset.sum_const, card_signedSquarefreeMultipliers, nsmul_eq_mul]; ring

end Ostmann.QuadraticSieve

end OAI
