import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMiddleBandGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionBlocks

namespace OAI

/-! # The complete middle-divisor correction, with the unit boundary retained -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticMiddleCorrectionTotal (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|)
    (M : ℝ) (e B N Q L : ℕ) (P : ℕ → ℕ → Prop)
    (v w : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Q, ∑ b ∈ oddSquarefreeRange (2 * B),
    if B ≤ b ∧ P d b then (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
      quadraticMiddleWindow ρ a ha M e N d v w b L else 0

theorem quadratic_whole_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M J : ℝ, 0 ≤ C →
      ∀ e B N Q L : ℕ, 0 < M → 0 < e → 0 < B → 0 < N → 1 ≤ Q → 1 ≤ J →
      ∀ P : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ d ∈ Finset.Icc 1 Q, ∀ b ∈ oddSquarefreeRange (2 * B), B ≤ b → P d b →
        quadraticCorrectionBase M N e B / (4 * J) ≤ (d : ℝ)) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionTotal ρ a ha M e B N Q L P v w‖ ≤
        (128 * J * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) *
            (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by
  classical
  obtain ⟨Cu, hCu, hcU⟩ := quadratic_middle_unit_growth ρ a ha
  obtain ⟨Cb, hCb, hcB⟩ := quadratic_middle_band_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M J hC e B N Q L hM he hB hN hQ hJ P v w hv hw hP hmat
  let S := quadraticCorrectionGrowthScale C ε ξ M e B N v w
  let U := 128 * J * (2 * L + 1) * Cu * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let V := 128 * J * (2 * L + 1) * Cb * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * S
  let F := fun d => ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
    ∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P d b then
      (((ArithmeticFunction.moebius d : ℂ) / d) / (Real.sqrt b : ℂ)) *
        quadraticMiddleWindow ρ a ha M e N d v w b L else 0
  have hS : 0 ≤ S := by dsimp [S, quadraticCorrectionGrowthScale]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hlog : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith
  have hunit : ‖F 1‖ ≤ U := by
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ 1
    · have hu := hcU C ε ξ M J hC e B N L hM he hB hN hJ hc (P 1) v w hv hw
        (by simpa only [pow_zero, Nat.div_one] using hmat 0 (Nat.zero_le _))
      have heq : F 1 = ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionUnit ρ a ha M e B N L (P 1) v w := by
        simp [F, quadraticMiddleCorrectionUnit]
      rw [heq]
      apply hu.trans
      change 128 * J * (2 * L + 1) * Cu * S ≤ U
      dsimp [U]
      nlinarith [mul_le_mul_of_nonneg_left hlog
        (show 0 ≤ 128 * J * (2 * L + 1) * Cu * S by positivity)]
    · have hz : F 1 = 0 := by
        dsimp [F]
        have hh : (∑ b ∈ oddSquarefreeRange (2 * B), if B ≤ b ∧ P 1 b then
            (((ArithmeticFunction.moebius 1 : ℂ) / 1) / (Real.sqrt b : ℂ)) *
              quadraticMiddleWindow ρ a ha M e N 1 v w b L else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          have hn : ¬ (B ≤ b ∧ P 1 b) := by
            intro h
            apply hc
            have hh := hP 1 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) b hb h.1 h.2
            have hid : quadraticCorrectionBase M N e B / (8 * J) =
                (quadraticCorrectionBase M N e B / (4 * J)) / 2 := by ring
            rw [hid]
            norm_num only [Nat.cast_one] at hh
            linarith
          simp only [hn, ite_false]
        simp only [Nat.cast_one]
        rw [hh, mul_zero]
      rw [hz, norm_zero]
      exact hU
  have hblock (j : ℕ) (_hj : j < Nat.log 2 Q + 1) :
      ‖∑ d ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), if d ≤ Q then F d else 0‖ ≤ V := by
    let D := 2 ^ j
    let P' := fun d b => d ≤ Q ∧ P d b
    have heq : (∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0) =
        ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionBand ρ a ha M e B N D L P' v w := by
      simp only [quadraticMiddleCorrectionBand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [F, P']
      by_cases hd : d ≤ Q
      · simp only [hd, ite_true, true_and, Finset.mul_sum]
      · simp only [hd, ite_false, false_and, and_false, Finset.sum_const_zero, mul_zero]
    change ‖∑ d ∈ Finset.Ioc D (2 * D), if d ≤ Q then F d else 0‖ ≤ V
    rw [heq]
    by_cases hc : quadraticCorrectionBase M N e B / (8 * J) ≤ (D : ℝ)
    · exact hcB C ε ξ M J hC e B N D L hM he hB hN
        (by dsimp [D]; positivity) hJ hc P' v w hv hw hmat
    · have hz : quadraticMiddleCorrectionBand ρ a ha M e B N D L P' v w = 0 := by
        unfold quadraticMiddleCorrectionBand
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro b hb
        have hn : ¬ (B ≤ b ∧ P' d b) := by
          intro h
          have hdp := (Finset.mem_Ioc.mp hd).1
          have hbound := hP d (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le D).trans_lt hdp), h.2.1⟩) b hb h.1 h.2.2
          apply hc
          have hhi : (d : ℝ) ≤ 2 * D := by exact_mod_cast (Finset.mem_Ioc.mp hd).2
          calc
            _ = (quadraticCorrectionBase M N e B / (4 * J)) / 2 := by ring
            _ ≤ (d : ℝ) / 2 := div_le_div_of_nonneg_right hbound (by norm_num)
            _ ≤ D := by linarith
        simp only [hn, ite_false]
      rw [hz, mul_zero, norm_zero]
      exact hV
  have hb := quadratic_correction_divisor_bound hQ F U (fun _ => V) hunit hblock
  have heq : (∑ d ∈ Finset.Icc 1 Q, F d) =
      ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticMiddleCorrectionTotal ρ a ha M e B N Q L P v w := by
    simp only [F, quadraticMiddleCorrectionTotal, Finset.mul_sum]
  rw [heq] at hb
  apply hb.trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [U, V, S]
  push_cast
  ring

end Ostmann

end OAI
