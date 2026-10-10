import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullSmallHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullSmallMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveWeight

namespace OAI

/-! # A common bound for the two literal small-kernel corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

noncomputable def quadraticSmallCorrectionScalar (C ε ξ M J : ℝ) (E N Q K L : ℕ) : ℝ :=
  (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + 8 * E * J * N))

theorem quadraticSmallCorrectionScalar_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (_hM : 0 ≤ M) (hJ : 0 ≤ J) (E N Q K L : ℕ) :
    0 ≤ quadraticSmallCorrectionScalar C ε ξ M J E N Q K L := by
  unfold quadraticSmallCorrectionScalar
  positivity

theorem quadraticSmallCorrectionScalar_scale (C ε ξ M J : ℝ) (E N Q K L : ℕ) :
    quadraticSmallCorrectionScalar C ε ξ M J E N Q K L =
      C * quadraticSmallCorrectionScalar 1 ε ξ M J E N Q K L := by
  unfold quadraticSmallCorrectionScalar
  ring

theorem quadraticSmallCorrectionScalar_mono {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hJ : 0 ≤ J) {E F N Q K L : ℕ} (hEF : E ≤ F) :
    quadraticSmallCorrectionScalar C ε ξ M J E N Q K L ≤
      quadraticSmallCorrectionScalar C ε ξ M J F N Q K L := by
  unfold quadraticSmallCorrectionScalar
  gcongr

theorem quadratic_small_combination_growth :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ E N Q K L : ℕ,
      0 < M → 1 ≤ E → 0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v : ℕ → ℂ,
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖(-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ)) *
          quadraticFullSmallHighCorrection M J E N Q K R v v +
        ((Real.sqrt M : ℂ) / 2) * quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v‖ ≤
        A * quadraticSmallCorrectionScalar C ε ξ M J E N Q K L * quadraticDivisorMoment (2 * N) v := by
  let I := ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)
  let W := quadraticSmallFourierBound quadraticSieveWeight
  have hW : 0 ≤ W := quadraticSmallFourierBound_nonneg _
  let A := 1 + 64 * ‖I‖ + 64 * W
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro C ε ξ M J hC hε hξ hξ' E N Q K L hM hE hN hQ hK hJ R v hmat
  let S := quadraticSmallCorrectionScalar C ε ξ M J E N Q K L * quadraticDivisorMoment (2 * N) v
  have hv : 0 ≤ quadraticDivisorMoment (2 * N) v := by unfold quadraticDivisorMoment; positivity
  have hS : 0 ≤ S := mul_nonneg
    (quadraticSmallCorrectionScalar_nonneg hC hM.le (by linarith) _ _ _ _ _) hv
  have hh := quadratic_full_small_high_growth hC hε hξ hξ' hM hE hN hQ hK hJ R v v hmat
  have hm := quadratic_full_small_middle_growth quadraticSieveWeight
    hC hε hξ hξ' hM hE hN hQ hK hJ (L := L) R v v hmat
  rw [Real.mul_self_sqrt hv] at hh hm
  have hhigh : ‖(Real.sqrt M : ℂ) * quadraticFullSmallHighCorrection M J E N Q K R v v‖ ≤ 64 * S := by
    apply hh.trans
    let T := ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
      ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
        (C * (4 * (K : ℝ) * N) ^ ε * (Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) + 8 * E * J * N)) *
          quadraticDivisorMoment (2 * N) v
    have hT : 0 ≤ T := by dsimp [T]; positivity
    calc
      _ = 64 * T := by dsimp [T]; ring
      _ ≤ 64 * ((2 * L + 1) * T) := by nlinarith [show 0 ≤ (L : ℝ) by positivity]
      _ = 64 * S := by dsimp [S, quadraticSmallCorrectionScalar, T]; ring
  have hmiddle : ‖(Real.sqrt M : ℂ) *
      quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v‖ ≤ 64 * W * S := by
    apply hm.trans_eq
    dsimp [S, W, quadraticSmallCorrectionScalar]
    ring
  let l := (Real.sqrt M : ℂ) * quadraticFullSmallHighCorrection M J E N Q K R v v
  let m := (Real.sqrt M : ℂ) * quadraticFullSmallMiddleCorrection quadraticSieveWeight M J E N Q K L R v v
  have hid : (Real.sqrt M : ℂ) / 2 = (1 / 2 : ℂ) * (Real.sqrt M : ℂ) := by ring
  rw [hid]
  simp only [mul_assoc]
  change ‖(-I) * l + (1 / 2 : ℂ) * m‖ ≤ A * S
  apply (norm_add_le _ _).trans
  rw [norm_mul (-I) l, norm_mul (1 / 2 : ℂ) m, norm_neg]
  have hl := mul_le_mul_of_nonneg_left hhigh (norm_nonneg I)
  have hm' := mul_le_mul (show ‖(1 / 2 : ℂ)‖ ≤ 1 by norm_num) hmiddle (norm_nonneg _) zero_le_one
  change ‖I‖ * ‖l‖ ≤ ‖I‖ * (64 * S) at hl
  change ‖(1 / 2 : ℂ)‖ * ‖m‖ ≤ 1 * (64 * W * S) at hm'
  dsimp only [A]
  nlinarith only [hl, hm', hS]

end Ostmann

end OAI
