import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallUnitGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallCorrectionGeometry
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionBlocks

namespace OAI

/-! # The complete small-kernel high-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticSmallHighTotal (E B N Q : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
      quadraticDivisorBilinear (2 * N) (2 * N) d
        v w b else 0

theorem quadratic_whole_small_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (P : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hP : ∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
      quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ))
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q P v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  classical
  let S := quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w
  let V := 16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => (Real.sqrt M : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius (E * d) : ℂ) / (E * d : ℕ)) / (Real.sqrt b : ℂ)) *
        quadraticDivisorBilinear (2 * N) (2 * N) d
          v w b else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticSmallCorrectionGrowthScale]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ V := by
    by_cases hc : Real.sqrt M / Real.sqrt B ≤ 8 * E * J
    · have hu := quadratic_small_high_unit_growth hC hE hM hB (by positivity) hc (P 1) v w
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = (Real.sqrt M : ℂ) * (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
          (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
            quadraticDivisorBilinear (2 * N) (2 * N) 1 v w b else 0) := by
        simp only [F, mul_one]
      rw [heq]
      apply hu.trans
      change 16 * S ≤ V
      dsimp [V]
      nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (((ArithmeticFunction.moebius E : ℂ) / E) / (Real.sqrt b : ℂ)) *
              quadraticDivisorBilinear (2 * N) (2 * N) 1
                v w b else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            have hbound := quadratic_small_correction_cutoff (D := 1) (d := 1)
              hM hJ (by omega : 0 < E) hB (by decide) h.1
              (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 (by norm_num)
              (hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2)
            simpa only [Nat.cast_one, mul_one] using hbound
          simp only [hn, ite_false]
        simp only [mul_one]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hV
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        (Real.sqrt M : ℂ) * quadraticSmallHighBand E B N D P' v w := by
      simp only [quadraticSmallHighBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : Real.sqrt M / (Real.sqrt B * D) ≤ 8 * E * J
    · exact quadratic_small_high_growth hC hE hM hB (by dsimp [D]; positivity)
        (by positivity) hc P' v w hmat
    · have hz : quadraticSmallHighBand E B N D P' v w = 0 := by
        unfold quadraticSmallHighBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          apply hc
          exact quadratic_small_correction_cutoff hM hJ (by omega : 0 < E)
            hB (by dsimp [D]; positivity) h.1
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
            (Finset.mem_Ioc.mp hd).2
            (hP d (Finset.mem_Icc.mpr
              ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2)
        simp only [hn, ite_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F V (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      (Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q P v w := by
    simp only [F, quadraticSmallHighTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [V, S]
  push_cast
  ring

end Ostmann

end OAI
