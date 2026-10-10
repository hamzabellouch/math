import OAI.NumberTheory.Ostmann.QuadraticSieveDualSquareLattice
import OAI.NumberTheory.Ostmann.QuadraticSieveSignedReindex
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem summable_dual_jacobi_series (W : 𝓢(ℝ, ℂ)) (e M : ℝ) (q : ℕ)
    (he : 0 < e) (hM : 0 < M) (hq : 0 < q) :
    Summable (fun h : ℤ => (jacobiSym h q : ℂ) *
      𝓕 W ((h : ℝ) * M / (e * q))) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hscale : e * (q : ℝ) / M ≠ 0 := ne_of_gt (by positivity)
  simpa only [div_div_eq_mul_div, mul_comm] using
    summable_weighted_jacobi (schwartz_summable_scaled (𝓕 W) (e * q / M) hscale) q

theorem jacobi_signed_square_factor (a : ℤ) (b c q : ℕ) [NeZero q] :
    jacobiSym (a * (b : ℤ) * (c : ℤ) ^ 2) q =
      if Nat.Coprime c q then jacobiSym (a * (b : ℤ)) q else 0 := by
  rw [show a * (b : ℤ) * (c : ℤ) ^ 2 = (c : ℤ) ^ 2 * (a * (b : ℤ)) by ring,
    jacobi_square_mul_left]
  simp only [Int.gcd_def, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one]
  rfl

theorem tsum_signed_jacobi_square_eq_dualSquareSum (W : 𝓢(ℝ, ℂ)) (a : ℤ)
    (e M : ℝ) (b q : ℕ) [NeZero q] :
    (∑' c : {c : ℕ // 0 < c},
      (jacobiSym (a * (b : ℤ) * (c.val : ℤ) ^ 2) q : ℂ) *
        𝓕 W (((a * (b : ℤ) * (c.val : ℤ) ^ 2 : ℤ) : ℝ) * M / (e * q))) =
      (jacobiSym (a * (b : ℤ)) q : ℂ) * dualSquareSum W (a : ℝ) e M (b : ℝ) q := by
  unfold dualSquareSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  have harg : (((a * (b : ℤ) * (c.val : ℤ) ^ 2 : ℤ) : ℝ) * M / (e * q)) =
      (a : ℝ) * (b : ℝ) * M * (c.val : ℝ) ^ 2 / (e * q) := by
    push_cast
    ring
  rw [harg, jacobi_signed_square_factor]
  split <;> simp_all only [Int.cast_zero, zero_mul, mul_zero]

theorem summable_dual_jacobi_pairs (W : 𝓢(ℝ, ℂ)) (a : ℤ) (e M : ℝ) (q : ℕ)
    (ha : a ≠ 0) (he : 0 < e) (hM : 0 < M) (hq : 0 < q) :
    Summable (fun p : OddSquarefreeIndex × {c : ℕ // 0 < c} =>
      (jacobiSym (a * (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2) q : ℂ) *
        𝓕 W (((a * (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2 : ℤ) : ℝ) * M / (e * q))) :=
  summable_signed_squarefree_pairs _ (summable_dual_jacobi_series W e M q he hM hq) ha

theorem summable_dualSquareSum_terms (W : 𝓢(ℝ, ℂ)) (a : ℤ) (e M : ℝ) (q : ℕ)
    (ha : a ≠ 0) (he : 0 < e) (hM : 0 < M) (hq : 0 < q) :
    Summable (fun b : OddSquarefreeIndex => (jacobiSym (a * (b.val : ℤ)) q : ℂ) *
      dualSquareSum W (a : ℝ) e M (b.val : ℝ) q) := by
  let : NeZero q := ⟨hq.ne'⟩
  apply (summable_dual_jacobi_pairs W a e M q ha he hM hq).prod.congr
  intro b
  exact tsum_signed_jacobi_square_eq_dualSquareSum W a e M b.val q

theorem dual_jacobi_series_eq_signed_dualSquareSum (W : 𝓢(ℝ, ℂ)) (e M : ℝ) (q : ℕ)
    (he : 0 < e) (hM : 0 < M) (hq : 1 < q) :
    (∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 W ((h : ℝ) * M / (e * q))) =
      ∑ a ∈ signedSquarefreeMultipliers, ∑' b : OddSquarefreeIndex,
        (jacobiSym (a * (b.val : ℤ)) q : ℂ) *
          dualSquareSum W (a : ℝ) e M (b.val : ℝ) q := by
  let : NeZero q := ⟨(Nat.zero_lt_of_lt hq).ne'⟩
  rw [tsum_int_eq_zero_add_signed_squarefree _
    (summable_dual_jacobi_series W e M q he hM (Nat.zero_lt_of_lt hq))]
  rw [jacobiSym.zero_left hq, Int.cast_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro a ha
  apply tsum_congr
  intro b
  exact tsum_signed_jacobi_square_eq_dualSquareSum W a e M b.val q

end Ostmann.QuadraticSieve

end OAI
