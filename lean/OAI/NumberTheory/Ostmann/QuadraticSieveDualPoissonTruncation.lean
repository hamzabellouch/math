import OAI.NumberTheory.Ostmann.QuadraticSieveDualTruncation
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussNorm

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def dualPoissonPrefix (W : 𝓢(ℝ, ℂ)) (M : ℝ) (k q K : ℕ) [NeZero q] : ℂ :=
  ∑ e ∈ k.divisors, ∑ a ∈ signedSquarefreeMultipliers,
    (μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
      gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar * (jacobiSym (e : ℤ) q : ℂ) *
      ∑ b ∈ oddSquarefreeUpTo K, (jacobiSym (a * (b : ℤ)) q : ℂ) *
        dualSquareSum W (a : ℝ) (e : ℝ) M (b : ℝ) q

noncomputable def dualPoissonTail (W : 𝓢(ℝ, ℂ)) (M : ℝ) (k q : ℕ) [NeZero q] (K : ℝ) : ℂ :=
  ∑ e ∈ k.divisors, ∑ a ∈ signedSquarefreeMultipliers,
    (μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
      gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar * (jacobiSym (e : ℤ) q : ℂ) *
      dualSquarefreeTail W a (e : ℝ) M q K

theorem coprime_quadratic_poisson_prefix_tail {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (hq1 : 1 < q)
    (k : ℕ) (hk : k ≠ 0) (M : ℝ) (hM : 0 < M) (W : 𝓢(ℝ, ℂ)) (K : ℕ) :
    (∑' m : ℤ, if Nat.Coprime m.natAbs k then
      (jacobiSym m q : ℂ) * W ((m : ℝ) / M) else 0) =
      dualPoissonPrefix W M k q K + dualPoissonTail W M k q K := by
  rw [coprime_quadratic_poisson_dual hq hsq hq1 k hk M hM W]
  unfold dualPoissonPrefix dualPoissonTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hepos : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
  have hj (b : OddSquarefreeIndex) :
      (jacobiSym ((e : ℤ) * a * (b.val : ℤ)) q : ℂ) =
        (jacobiSym (e : ℤ) q : ℂ) * (jacobiSym (a * (b.val : ℤ)) q : ℂ) := by
    rw [mul_assoc, jacobiSym.mul_left, Int.cast_mul]
  simp_rw [hj, mul_assoc (jacobiSym (e : ℤ) q : ℂ)]
  rw [tsum_mul_left, dualSquarefree_prefix_tail W a (e : ℝ) M q K
    (signedSquarefreeMultiplier_ne_zero ha) hepos hM (by omega)]
  ring

theorem dualPoissonTail_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (k q : ℕ) [NeZero q] (K : ℝ),
      0 < M → k ≠ 0 → Odd q → Squarefree q → 0 < K →
      ‖dualPoissonTail W M k q K‖ ≤
        C * ∑ e ∈ k.divisors,
          (M / (e * q)) * Real.sqrt (q : ℝ) /
            ((M / (e * q)) ^ (A + 2) * K ^ A) := by
  obtain ⟨C,hC,hbound⟩ := dualSquarefreeTail_bound W A
  refine ⟨4*C, by positivity, ?_⟩
  intro M k q _ K hM hk hq hsq hK
  have hqp : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hnorm : ‖gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
    rw [← quadratic_gauss_norm_sq hq hsq, Real.sqrt_sq (norm_nonneg _)]
  unfold dualPoissonTail
  calc
    _ ≤ ∑ e ∈ k.divisors, ∑ a ∈ signedSquarefreeMultipliers,
        ‖(μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
          gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
          (jacobiSym (e : ℤ) q : ℂ) * dualSquarefreeTail W a e M q K‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ e ∈ k.divisors, ∑ _a ∈ signedSquarefreeMultipliers,
        (M / (e * q)) * Real.sqrt (q : ℝ) *
          (C / ((M / (e * q)) ^ (A + 2) * K ^ A)) := by
      apply Finset.sum_le_sum
      intro e he
      have hep : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
      have hqr : (0 : ℝ) < q := by exact_mod_cast hqp
      apply Finset.sum_le_sum
      intro a ha
      have hj : ‖(jacobiSym (e : ℤ) q : ℂ)‖ ≤ 1 := by
        rcases jacobiSym.trichotomy (e : ℤ) q with h | h | h <;> simp [h]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity), hnorm]
      have hb := hbound a e M q K (signedSquarefreeMultiplier_ne_zero ha) hep hM hqp hK
      calc
        _ ≤ 1 * (M / (e * q)) * Real.sqrt (q : ℝ) * 1 *
            (C / ((M / (e * q)) ^ (A + 2) * K ^ A)) := by
          gcongr
          exact norm_moebius_complex_le_one e
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, card_signedSquarefreeMultipliers, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring

end Ostmann.QuadraticSieve

end OAI
