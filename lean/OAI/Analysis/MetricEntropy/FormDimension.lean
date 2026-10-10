import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OAI

universe uK

/-!
# Dimension of symmetric-form coefficients

The coefficients of a symmetric `j`-linear form on an `r`-dimensional space
are indexed by multisets of `j` basis vectors. Their number gives the
dimension of the coefficient space and hence its cardinality over a finite field.
-/

namespace MetricEntropyDuality

/-- The number of multisets of `j` basis vectors chosen from `r` vectors. -/
def formDimension (r j : ℕ) : ℕ := (r + j - 1).choose j

/-- Positive ambient dimension gives a nonempty coefficient index set. -/
theorem formDimension_pos {r j : ℕ} (hr : 0 < r) : 0 < formDimension r j := by
  exact Nat.choose_pos (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left hr))

/-- Stars and bars counts the actual multiset coefficient indices. -/
theorem card_sym_fin (r j : ℕ) :
    Fintype.card (Sym (Fin r) j) = formDimension r j := by
  simpa only [Fintype.card_fin, formDimension] using
    (Sym.card_sym_eq_choose (α := Fin r) j)

/-- A coefficient function over `ZMod p` has exactly `p` choices at each index. -/
theorem card_form_coefficients (p r j : ℕ) [NeZero p] :
    Fintype.card (Sym (Fin r) j → ZMod p) = p ^ formDimension r j := by
  classical
  rw [Fintype.card_fun, ZMod.card, card_sym_fin]

/-- The coefficient space has one independent scalar coordinate per multiset. -/
theorem finrank_form_coefficients (K : Type uK) [Field K] (r j : ℕ) :
    Module.finrank K (Sym (Fin r) j → K) = formDimension r j := by
  rw [Module.finrank_fintype_fun_eq_card, card_sym_fin]

end MetricEntropyDuality

end OAI
