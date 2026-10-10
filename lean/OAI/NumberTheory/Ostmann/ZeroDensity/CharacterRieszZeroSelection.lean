import OAI.NumberTheory.Ostmann.ZeroDensity.RieszSingleZeroRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterNearZeroSimple

namespace OAI

/-! # The unique actual zero contribution selected by a Riesz rectangle -/

namespace Ostmann

open Complex Set
open scoped Interval

noncomputable def characterRieszZeroTerm (χ : PrimitiveComplexCharacter) (X : ℝ)
    (e : Option ℕ) : ℂ :=
  match e with
  | none => 0
  | some i => -rieszContourWeight X ((actualCharacterZeros χ).zeros i)

theorem character_zero_enumerated_of_re_pos (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) (hz : χ.L s = 0) :
    ∃ i, (actualCharacterZeros χ).zeros i = s := by
  apply actualCharacterZeros_complete
  refine ⟨hs, ?_, hz⟩
  by_contra hn
  exact χ.L_ne_zero_one_le_re s (not_lt.mp hn) hz

theorem character_riesz_zero_selection (χ : PrimitiveComplexCharacter) (a T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hleft : ∀ s : ℂ, s.re = a → |s.im| ≤ T → χ.L s ≠ 0)
    (hreal : ∀ i : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1)
    (hunique : ∀ i j : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
      a ≤ ((actualCharacterZeros χ).zeros j).re →
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      |((actualCharacterZeros χ).zeros j).im| ≤ T → i = j) :
    ∃ e : Option ℕ,
      (∀ i : ℕ, e = some i → a < ((actualCharacterZeros χ).zeros i).re ∧
        χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
      (∀ i : ℕ, a ≤ ((actualCharacterZeros χ).zeros i).re →
        |((actualCharacterZeros χ).zeros i).im| ≤ T → e = some i) ∧
      ∀ X b : ℝ, 0 < X → 1 < b →
        rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
          a b (-T) T = I * (((2 * Real.pi : ℝ) : ℂ) * characterRieszZeroTerm χ X e) := by
  classical
  let Z := actualCharacterZeros χ
  by_cases hex : ∃ i : ℕ, a ≤ (Z.zeros i).re ∧ |(Z.zeros i).im| ≤ T
  · obtain ⟨i, hi, hit⟩ := hex
    obtain ⟨hsq, him, hm⟩ := hreal i hi hit
    change (Z.zeros i).im = 0 at him
    have hai : a < (Z.zeros i).re := by
      apply lt_of_le_of_ne hi
      intro he
      exact hleft (Z.zeros i) he.symm hit (Z.actual_zero i)
    refine ⟨some i, ?_, ?_, ?_⟩
    · intro j hj
      cases Option.some.inj hj
      exact ⟨hai, hsq, him⟩
    · intro j hj hjt
      rw [hunique j i hj hi hjt hit]
    · intro X b hX hb
      have hzeros (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) (hz : χ.L s = 0) :
          s = Z.zeros i := by
        have hab : a ≤ b := ha1.le.trans hb.le
        have hsr : a ≤ s.re := ((uIcc_of_le hab) ▸ hs.1).1
        have hst : |s.im| ≤ T := by
          apply abs_le.mpr
          simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hs.2
        obtain ⟨j, hj⟩ := character_zero_enumerated_of_re_pos χ s (ha.trans_le hsr) hz
        have hji := hunique j i (by simpa only [hj] using hsr) hi
          (by simpa only [hj] using hst) hit
        change Z.zeros j = s at hj
        simpa only [hji] using hj.symm
      have hr := rieszContour_single_zero_rectangle χ X hX a b (-T) T (Z.zeros i)
        ha hai ((Z.in_strip i).2.trans hb) (by simpa only [him] using neg_neg_of_pos hT)
        (by simpa only [him] using hT) hzeros
      rw [hm] at hr
      simp only [Nat.cast_one, one_mul] at hr
      rw [hr]
      simp only [characterRieszZeroTerm]
      push_cast
      ring
  · refine ⟨none, by simp, ?_, ?_⟩
    · intro i hi hit
      exact (hex ⟨i, hi, hit⟩).elim
    · intro X b hX hb
      have hab : a ≤ b := ha1.le.trans hb.le
      have hzero := rieszContour_rectangle_zero χ X hX a b (-T) T ha hab
      have hn (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) : χ.L s ≠ 0 := by
        intro hz
        have hsr : a ≤ s.re := ((uIcc_of_le hab) ▸ hs.1).1
        have hst : |s.im| ≤ T := by
          apply abs_le.mpr
          simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hs.2
        obtain ⟨i, hi⟩ := character_zero_enumerated_of_re_pos χ s (ha.trans_le hsr) hz
        change Z.zeros i = s at hi
        exact hex ⟨i, by simpa only [hi] using hsr, by simpa only [hi] using hst⟩
      rw [hzero hn]
      simp [characterRieszZeroTerm]

end Ostmann

end OAI
