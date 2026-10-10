import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.Ostmann.Construction.TransferGraph

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

def anchorSignPair (α ε : ℤ) (t : Bool) : ℤ × ℤ :=
  if t then (1, -α * ε) else (-α * ε, 1)

theorem transferCopySign_sq (t : Bool) : transferCopySign t ^ 2 = 1 := by
  cases t <;> rfl

theorem transferCopySign_injective : Function.Injective transferCopySign := by
  intro a b h
  cases a <;> cases b <;> simp_all [transferCopySign]

/-- Normalize by the new bulk parity. Its inverse equals itself, since it is
a sign. Both entries come directly from the copied graph, including the
cross-copy incoming-pivot coefficient. -/
theorem transferred_anchor_pair {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H) (α ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (hincoming : b (some (.inl a)) (some (.inl i)) = ε)
    (hpivot : b (some (.inl a)) none = α) (t : Bool) :
    (transferCopySign t * ε * transferredGraph b (.inl (true, a)) (.inl (t, i)),
      transferCopySign t * ε * transferredGraph b (.inl (false, a)) (.inl (t, i))) =
      anchorSignPair α ε t := by
  rcases hε with rfl | rfl <;> cases t <;>
    simp [anchorSignPair, transferredGraph, transferCopySign, hincoming, hpivot]

/-- Once created, an outside anchor's normalized code is unchanged by every
later bulk copy. -/
theorem transferred_anchor_code_preserved {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y) (i : H)
    (ε : ℤ) (t : Bool) :
    (transferCopySign t * ε) * transferredGraph b (.inr y) (.inl (t, i)) =
      ε * b (some (.inr y)) (some (.inl i)) := by
  cases t <;> simp [transferredGraph, transferCopySign]

theorem anchorSignPair_determines_parity (α ε ε' : ℤ) (t t' : Bool)
    (hα : α = 1 ∨ α = -1)
    (h : anchorSignPair α ε t = anchorSignPair α ε' t') : ε = ε' := by
  rcases hα with rfl | rfl <;> cases t <;> cases t' <;>
    simp only [anchorSignPair, Bool.false_eq_true, ite_false, ite_true,
      Prod.mk.injEq, neg_one_mul, neg_neg, one_mul] at h <;> omega

def copyPathParity (t : ℕ → Bool) : ℕ → ℤ
  | 0 => 1
  | j + 1 => transferCopySign (t j) * copyPathParity t j

theorem copyPathParity_sign (t : ℕ → Bool) (j : ℕ) :
    copyPathParity t j = 1 ∨ copyPathParity t j = -1 := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    rcases ih with h | h <;> cases ht : t j <;>
      simp [copyPathParity, ht, transferCopySign, h]

def finiteCopyPath {n : ℕ} (t : Fin n → Bool) (j : ℕ) : Bool :=
  if h : j < n then t ⟨j, h⟩ else false

def finiteAnchorCode {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool) : Fin n → ℤ × ℤ :=
  fun j => anchorSignPair (α j) (copyPathParity (finiteCopyPath t) j) (t j)

def finalCopyParity {n : ℕ} (t : Fin n → Bool) : ℤ := copyPathParity (finiteCopyPath t) n

theorem finiteAnchorCode_prefix_parity {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t t' : Fin n → Bool)
    (hcode : finiteAnchorCode α t = finiteAnchorCode α t') (j : Fin n) :
    copyPathParity (finiteCopyPath t) j = copyPathParity (finiteCopyPath t') j := by
  exact anchorSignPair_determines_parity _ _ _ _ _ (hα j) (congrFun hcode j)

/-- All code pairs determine the incoming parities; the final parity then
determines the last copy sign as well. -/
theorem finiteAnchorCode_final_injective {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) :
    Function.Injective (fun t : Fin n → Bool => (finiteAnchorCode α t, finalCopyParity t)) := by
  intro t t' he
  have hcode := congrArg Prod.fst he
  have hfinal := congrArg Prod.snd he
  funext j
  have hbefore := finiteAnchorCode_prefix_parity α hα t t' hcode j
  have hafter : copyPathParity (finiteCopyPath t) (j.val + 1) =
      copyPathParity (finiteCopyPath t') (j.val + 1) := by
    by_cases hj : j.val + 1 < n
    · exact finiteAnchorCode_prefix_parity α hα t t' hcode ⟨j.val + 1, hj⟩
    · have hjn : j.val + 1 = n := by omega
      simpa only [hjn, finalCopyParity] using hfinal
  simp only [copyPathParity, finiteCopyPath, j.isLt, dite_true, Fin.eta] at hafter
  rw [hbefore] at hafter
  apply transferCopySign_injective
  exact mul_right_cancel₀ (by rcases copyPathParity_sign (finiteCopyPath t') j with h | h <;> omega) hafter

/-- There are at most two paths with any fixed anchor code. -/
theorem card_anchorCode_fiber_le_two {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (code : Fin n → ℤ × ℤ) :
    Fintype.card {t : Fin n → Bool // finiteAnchorCode α t = code} ≤ 2 := by
  classical
  let f : {t : Fin n → Bool // finiteAnchorCode α t = code} → Bool :=
    fun t => decide (finalCopyParity t.val = 1)
  have hf : Function.Injective f := by
    intro t t' he
    apply Subtype.ext
    apply finiteAnchorCode_final_injective α hα
    apply Prod.ext
    · exact t.property.trans t'.property.symm
    · have ht := copyPathParity_sign (finiteCopyPath t.val) n
      have ht' := copyPathParity_sign (finiteCopyPath t'.val) n
      change decide (finalCopyParity t.val = 1) = decide (finalCopyParity t'.val = 1) at he
      rcases ht with ht | ht <;> rcases ht' with ht' | ht' <;>
        simp only [finalCopyParity] at he ⊢ <;> simp_all
  simpa only [Fintype.card_bool] using Fintype.card_le_of_injective f hf

end Ostmann

end OAI
