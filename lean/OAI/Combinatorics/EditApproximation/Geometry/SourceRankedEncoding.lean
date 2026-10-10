import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram
import Mathlib.Data.Nat.Log
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! An explicit parity tag separates source coordinates and table keys.
The code is computed from coordinates without enumerating the key type. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



def keyCapacity (sourceCapacity tableCapacity : ℕ) : ℕ :=
  2 * (sourceCapacity + tableCapacity)

def keyBits (sourceCapacity tableCapacity : ℕ) : ℕ :=
  Nat.clog 2 (keyCapacity sourceCapacity tableCapacity + 1)

 theorem keyCode_injective (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (hs : Function.Injective sourceCode) (ht : Function.Injective tableCode) :
    Function.Injective (keyCode sourceCode tableCode) := by
  intro left right h
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have heq : sourceCode left = sourceCode right := by
        change 2 * sourceCode left = 2 * sourceCode right at h
        omega
      exact congrArg Sum.inl (hs heq)
    | inr right =>
      change 2 * sourceCode left = 2 * tableCode right + 1 at h
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * tableCode left + 1 = 2 * sourceCode right at h
      omega
    | inr right =>
      have heq : tableCode left = tableCode right := by
        change 2 * tableCode left + 1 = 2 * tableCode right + 1 at h
        omega
      exact congrArg Sum.inr (ht heq)

 theorem keyCode_bound (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (sourceCapacity tableCapacity : ℕ)
    (hs : ∀ source, sourceCode source < sourceCapacity)
    (ht : ∀ table, tableCode table < tableCapacity) (key : Sum σ κ) :
    keyCode sourceCode tableCode key < keyCapacity sourceCapacity tableCapacity := by
  cases key with
  | inl source => have := hs source; dsimp [keyCode, keyCapacity]; omega
  | inr table => have := ht table; dsimp [keyCode, keyCapacity]; omega

 theorem keyCode_fits (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (sourceCapacity tableCapacity : ℕ)
    (hs : ∀ source, sourceCode source < sourceCapacity)
    (ht : ∀ table, tableCode table < tableCapacity) (key : Sum σ κ) :
    keyCode sourceCode tableCode key < 2 ^ keyBits sourceCapacity tableCapacity :=
  (keyCode_bound sourceCode tableCode sourceCapacity tableCapacity hs ht key).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

end EditApproximation.SourceRanked

end OAI
