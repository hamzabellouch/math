import OAI.NumberTheory.Ostmann.Arithmetic.NodeBulkProducts
import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryEnergy

namespace OAI

/-! # The literal child products in the original prime-sampled history -/

namespace Ostmann
open scoped BigOperators Classical

theorem actualChildProducts_indexed_natCast (n : ℕ) (x : TreeLeafIndex n → ℕ) :
    actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (x i : ℤ))) =
      (actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm x)).map
        (fun z => ((z.1 : ℤ), (z.2 : ℤ))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → ℕ at x
    let a : TreeLeafIndex n → ℕ := fun i => x (.inl i)
    let b : TreeLeafIndex n → ℕ := fun i => x (.inr i)
    change
      (treeLeafProduct n ((treeLeafTupleEquiv ℤ n).symm (fun i => (a i : ℤ))),
       treeLeafProduct n ((treeLeafTupleEquiv ℤ n).symm (fun i => (b i : ℤ)))) ::
        (actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (a i : ℤ))) ++
         actualChildProducts n ((treeLeafTupleEquiv ℤ n).symm (fun i => (b i : ℤ)))) =
      ((treeLeafProduct n ((treeLeafTupleEquiv ℕ n).symm a),
        treeLeafProduct n ((treeLeafTupleEquiv ℕ n).symm b)) ::
        (actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm a) ++
         actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm b))).map
           (fun z : ℕ × ℕ => ((z.1 : ℤ), (z.2 : ℤ)))
    rw [List.map_cons, List.map_append, ih, ih]
    simp only [treeLeafProduct_indexed, Nat.cast_prod]

theorem sampledPrimeHistory_bulk_indexed (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) :
    (sampledPrimeHistory P Q n hunit x pivots).bulk =
      (treeLeafTupleEquiv ℤ n).symm (fun i => ((x i : ℕ) : ℤ)) := by
  apply (treeLeafTupleEquiv ℤ n).injective
  funext i
  simp only [sampledPrimeHistory, treeLeafTupleEquiv_map, Equiv.apply_symm_apply]

theorem sampledPrimeHistory_childProducts (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) (j : Fin (2 ^ n - 1)) :
    ((sampledPrimeHistory P Q n hunit x pivots).leftProduct j,
     (sampledPrimeHistory P Q n hunit x pivots).rightProduct j) =
      ((((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm (fun i => (x i : ℕ)))).getD j.val (1, 1)).1 : ℤ),
       (((actualChildProducts n ((treeLeafTupleEquiv ℕ n).symm (fun i => (x i : ℕ)))).getD j.val (1, 1)).2 : ℤ)) := by
  change (actualChildProducts n (sampledPrimeHistory P Q n hunit x pivots).bulk).getD j.val (1, 1) = _
  rw [sampledPrimeHistory_bulk_indexed, actualChildProducts_indexed_natCast]
  exact List.getD_map _ (1, 1) (fun z : ℕ × ℕ => ((z.1 : ℤ), (z.2 : ℤ)))

end Ostmann

end OAI
