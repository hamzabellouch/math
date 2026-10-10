import OAI.NumberTheory.Ostmann.Characters.CharacterHBounds
import OAI.NumberTheory.Ostmann.Characters.CharacterTargetGaps

namespace OAI

/-! # The actual backwards targets give the copied block's exact center -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterLogCenter {k : ℕ} (J : ℝ) (T : Fin k → ℝ)
    (a : Fin k → Bool → ℝ) (F : ℝ) (v : CharacterRole k) : ℝ :=
  match v.2 with
  | none => J
  | some (.inl j) => T j
  | some (.inr (.inl (j, b))) => a j b
  | some (.inr (.inr _)) => F

noncomputable def characterPivotTarget (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (j : Fin k) : ℝ :=
  (pivotTargets k J a Δ)[j.val]'(by simp only [pivotTargets, backwardTargets_length,
    pivotCoefficients, List.length_ofFn]; exact j.isLt)

private theorem sum_drop_eq_sum_later (s : List ℝ) (k : ℕ) (hlen : s.length = k) (n : ℕ) :
    (s.drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, s[j.val.val]'(by rw [hlen]; exact j.val.isLt) := by
  let e : Fin (s.drop (n + 1)).length ≃ {j : Fin k // n < j.val} :=
    { toFun := fun i => ⟨⟨n + 1 + i.val, by
        have hi := i.isLt
        simp only [List.length_drop, hlen] at hi
        omega⟩, by change n < n + 1 + i.val; omega⟩
      invFun := fun j => ⟨j.val.val - (n + 1), by
        simp only [List.length_drop, hlen]
        have hj := j.val.isLt
        have hn := j.property
        omega⟩
      left_inv := by intro i; apply Fin.ext; dsimp; omega
      right_inv := by intro j; apply Subtype.ext; apply Fin.ext; dsimp; have := j.property; omega }
  have hsum : (∑ i : Fin (s.drop (n + 1)).length, (s.drop (n + 1))[i.val]) =
      (s.drop (n + 1)).sum := by
    rw [← List.sum_ofFn, List.ofFn_getElem]
  rw [← hsum]
  apply Fintype.sum_equiv e
  intro i
  simp only [List.getElem_drop]
  rfl

theorem characterPivotTarget_future (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) (n : ℕ) :
    ((pivotTargets k J a Δ).drop (n + 1)).sum =
      ∑ j : {j : Fin k // n < j.val}, characterPivotTarget k J a Δ j.val :=
  sum_drop_eq_sum_later _ k (by simp [pivotTargets, backwardTargets_length, pivotCoefficients]) n

/-- This is the equality log H = T_j + Delta_j used by the transfer.
It follows from the constructed backwards targets, not a range assumption. -/
theorem character_H_target_center {k n : ℕ} (hn : n < k) (J B z m F : ℝ)
    (a : Fin k → Bool → ℝ) :
    let Δ := fun j : Fin k => characterPivotGap B z m j.val
    let A := fun j => a j false + a j true
    let T := characterPivotTarget k J A Δ
    (∑ h : CopyScheduleH (characterRole k) n,
      characterLogCenter J T a F (copyScheduleOrigin n h.val)) =
        T ⟨n, hn⟩ + characterPivotGap B z m n := by
  intro Δ A T
  rw [character_H_sum hn]
  simp only [characterLogCenter, characterPivotAtom, characterAnchorAtom, Fintype.sum_bool]
  have ht := pivotTargets_recurrence k J A Δ ⟨n, hn⟩
  rw [characterPivotTarget_future] at ht
  change T ⟨n, hn⟩ = (2 : ℝ) ^ n * J + (a ⟨n, hn⟩ false + a ⟨n, hn⟩ true) -
    characterPivotGap B z m n + ∑ j : {j : Fin k // n < j.val}, T j.val at ht
  linarith

end Ostmann

end OAI
