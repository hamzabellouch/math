import OAI.NumberTheory.Ostmann.Characters.TemplateLeafSymbolic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι : Type*}

def indexedBottomExpressions (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) :
    Fin (2^j) → BottomExpression (ι:=ι) k := fun i =>
  (bottomExpressions k j b s e t).get
    ((finCongr (bottomExpressions_length k j b s e t).symm) i)

theorem indexedBottomExpressions_mem (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (i : Fin (2^j)) :
    indexedBottomExpressions k j b s e t i ∈ bottomExpressions k j b s e t :=
  List.get_mem _ _

theorem indexedBottomExpressions_prod {M : Type*} [CommMonoid M]
    (k j : ℕ) (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j)
    (t : HistoryReconstruction.Tree j) (F : BottomExpression (ι:=ι) k → M) :
    (∏ i : Fin (2^j), F (indexedBottomExpressions k j b s e t i)) =
      ((bottomExpressions k j b s e t).map F).prod := by
  exact ((finCongr (bottomExpressions_length k j b s e t).symm).prod_comp
    (fun i => F ((bottomExpressions k j b s e t).get i))).trans
      (Fin.prod_univ_fun_getElem _ _)

theorem indexedBottomExpressions_forall (k j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
    (P : BottomExpression (ι:=ι) k → Prop) :
    (∀ i, P (indexedBottomExpressions k j b s e t i)) ↔
      ∀ z ∈ bottomExpressions k j b s e t, P z := by
  rw [List.forall_mem_iff_get]
  constructor
  · intro h i
    have hi := h ((finCongr (bottomExpressions_length k j b s e t).symm).symm i)
    simpa only [indexedBottomExpressions,Equiv.apply_symm_apply] using hi
  · intro h i
    exact h _

theorem weight_eq_fixed_symbolic_profiles (k : ℕ) (mask : (j:ℕ) → ℤ → State k j → Prop)
    (X Δ W : ℝ) (hX : 0 < X) (j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (h : WeightSupport k mask X Δ W j s (evalExpressions a e) t) :
    conjugateBy b (weight k mask X Δ W j s (evalExpressions a e) t) =
      ∏ i : Fin (2^j), profileValue k X
        (evalBottom k a (indexedBottomExpressions k j b s e t i)) := by
  rw [indexedBottomExpressions_prod k j b s e t (fun z => profileValue k X (evalBottom k a z))]
  exact weight_eq_symbolic_profiles k mask X Δ W hX j b s e t a h

theorem indexedBottomExpressions_period_good (k : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (j : ℕ) (b : Bool) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (h : Supported k B V j s (evalExpressions a e) t) (i : Fin (2^j)) :
    HistoryReconstruction.Good a
      (periodExpression k (indexedBottomExpressions k j b s e t i).2.2) :=
  finiteProductExpression_good _ a
    (bottomExpressions_good k B V j b s e t a he h _
      (indexedBottomExpressions_mem k j b s e t i))

end Ostmann.Characters.Template

end

end OAI
