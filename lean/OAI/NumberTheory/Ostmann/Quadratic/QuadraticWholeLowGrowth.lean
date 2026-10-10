import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitCorrectionGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionBlocks

namespace OAI

/-! # The complete low-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticLowCorrectionTotal (B N Q : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (ArithmeticFunction.moebius d : ℂ) *
      quadraticGaussDivisorBilinear (2 * N) (2 * N) d
        (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0

theorem quadratic_whole_low_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      (d : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  classical
  let S := quadraticCorrectionGrowthScale C ε ξ M e B N v w
  let V := 96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => ((M / e : ℝ) : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (ArithmeticFunction.moebius d : ℂ) *
        quadraticGaussDivisorBilinear (2 * N) (2 * N) d
          (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : 1 ≤ 2 * quadraticCorrectionBase M N e B * J
    · have hu := quadratic_low_unit_growth hC hM he hB hN hJ hc (P 1) v w hv hw
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = ((M / e : ℝ) : ℂ) * quadraticLowCorrectionUnit B N (P 1) v w := by
        simp [F, quadraticLowCorrectionUnit]
      rw [heq]
      apply hu.trans
      change 96 * J * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 96 * J * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (ArithmeticFunction.moebius 1 : ℂ) *
              quadraticGaussDivisorBilinear (2 * N) (2 * N) 1
                (quadraticSqrtNormalize v) (quadraticSqrtNormalize w) b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            simpa only [Nat.cast_one] using
              hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2
          simp only [hn, ite_false]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        ((M / e : ℝ) : ℂ) * quadraticLowCorrectionBand B N D P' v w := by
      simp only [quadraticLowCorrectionBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J
    · exact quadratic_low_band_growth hC hM he hB hN (by dsimp [D]; positivity)
        hJ hc P' v w hv hw hmat
    · have hz : quadraticLowCorrectionBand B N D P' v w = 0 := by
        unfold quadraticLowCorrectionBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          have hbound := hP d (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2
          exact hc ((by exact_mod_cast hdp.le : (D : ℝ) ≤ d).trans hbound)
        simp only [hn, ite_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      ((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q P v w := by
    simp only [F, quadraticLowCorrectionTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
  push_cast
  ring

end Ostmann

end OAI
