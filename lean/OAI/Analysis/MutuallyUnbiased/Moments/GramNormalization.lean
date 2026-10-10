import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import OAI.Analysis.MutuallyUnbiased.Certificate.AuxiliaryInterpretation

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

structure Key where
  leftTag : Fin 2
  rightTag : Fin 2
  rows : List (ℤ × ℤ)
  deriving DecidableEq, Repr

def rowOrder (a v : Charge) : List Coord :=
  (List.finRange 6).insertionSort (fun i j => (compare (a i) (a j) |>.then (compare (v i) (v j))) != .gt)

def orderedKey (s t : Fin 2) (a v : Charge) : Key :=
  ⟨s, t, (rowOrder a v).map (fun i => (a i, v i))⟩

def normalize (s t : Fin 2) (a v : Charge) : Key :=
  if (compare s.val t.val |>.then (compare (List.ofFn a) (List.ofFn v))) == .gt then
    orderedKey t s v a
  else orderedKey s t a v

def Key.leftCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).1
def Key.rightCharge (K : Key) : Charge := fun i => (K.rows.getD i.val (0, 0)).2

noncomputable def eval (B : Fin 7 → Basis) (K : Key) : ℝ :=
  auxiliaryMixedEntry B K.leftTag K.rightTag K.leftCharge K.rightCharge

theorem rowOrder_length (a v : Charge) : (rowOrder a v).length = 6 := by
  simp [rowOrder]

theorem rowOrder_nodup (a v : Charge) : (rowOrder a v).Nodup := by
  exact (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_finRange 6)

def rowAt (a v : Charge) (i : Coord) : Coord :=
  (rowOrder a v).get ⟨i.val, by rw [rowOrder_length]; exact i.isLt⟩

theorem rowAt_injective (a v : Charge) : Function.Injective (rowAt a v) := by
  intro i j hij
  have h := (rowOrder_nodup a v).injective_get hij
  exact Fin.ext (congrArg (fun x => x.val) h)

noncomputable def rowPermutation (a v : Charge) : Equiv.Perm Coord :=
  Equiv.ofBijective (rowAt a v)
    ⟨rowAt_injective a v, Finite.surjective_of_injective (rowAt_injective a v)⟩

theorem orderedKey_leftCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).leftCharge = a ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.leftCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem orderedKey_rightCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).rightCharge = v ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.rightCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem auxiliaryMixedEntry_row_permutation (B : Fin 7 → Basis)
    (s t : Fin 2) (a v : Charge) (π : Equiv.Perm Coord) :
    auxiliaryMixedEntry B s t (a ∘ π) (v ∘ π) = auxiliaryMixedEntry B s t a v := by
  have h : gramCharges (a ∘ π) (v ∘ π) = fun i j => gramCharges a v (π i) j := rfl
  simp only [auxiliaryMixedEntry, h, mixedMoment_row_permutation]

theorem auxiliaryMixedEntry_symm (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    auxiliaryMixedEntry B s t a v = auxiliaryMixedEntry B t s v a := by
  rw [← auxiliaryGram_eq B hB, ← auxiliaryGram_eq B hB, realGram_symm]

theorem eval_orderedKey (B : Fin 7 → Basis) (s t : Fin 2) (a v : Charge) :
    eval B (orderedKey s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold eval
  rw [orderedKey_leftCharge, orderedKey_rightCharge]
  exact auxiliaryMixedEntry_row_permutation B s t a v (rowPermutation a v)

theorem eval_normalize (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    eval B (normalize s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold normalize
  split <;> rw [eval_orderedKey]
  exact auxiliaryMixedEntry_symm B hB t s v a

end MUB6.GramNormalization

end OAI
