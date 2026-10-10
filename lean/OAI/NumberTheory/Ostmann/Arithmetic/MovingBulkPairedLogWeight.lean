import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkPairedCutoffs

namespace OAI

/-! # The fixed outside factor in the two actual bulk leaf weights -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingBulkLeafProduct_eq_cutoffs {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ a, 0 < value a)
    (outside : List ℕ) (cb cd : ℝ) (n : ℕ) (bulk : TreeLeafTuple (List σ) n) :
    treeLeafProduct (U := ℝ) n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) =
      logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ (2 ^ n) *
        treeLeafProduct n (treeLeafMap (fun slots =>
          bulkLogCutoffWeight (fun a => (value a : ℝ)) cb slots) n bulk) := by
  simp only [treeLeafProduct_eq_prod, treeLeafTupleEquiv_map,
    movingBulkListLogWeight_eq_cutoff value hvalue, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, card_treeLeafIndex]
  ring

theorem movingBulkLeafProduct_pair_eq_cutoffs {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ a, 0 < value a)
    (outside : List ℕ) (cb cd : ℝ) (n : ℕ) (bulk : Bool → TreeLeafTuple (List σ) n) :
    (treeLeafProduct (U := ℝ) n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n (bulk false)) : ℂ) *
        star (treeLeafProduct (U := ℝ) n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n (bulk true)) : ℂ) =
      (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
        (2 ^ n + 2 ^ n) : ℝ) *
        ((∏ j, bulkLogCutoffWeight (fun a => (value a : ℝ)) cb
          (movingBulkPairedCutoffSlots n bulk j) : ℝ) : ℂ) := by
  rw [movingBulkLeafProduct_eq_cutoffs value hvalue outside cb cd n (bulk false),
    movingBulkLeafProduct_eq_cutoffs value hvalue outside cb cd n (bulk true),
    movingBulkPairedCutoffSlots_product]
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal, pow_add,
    Complex.ofReal_pow, map_pow]
  ring

end Ostmann

end OAI
