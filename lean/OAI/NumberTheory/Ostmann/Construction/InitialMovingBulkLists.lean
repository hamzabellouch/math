import OAI.NumberTheory.Ostmann.Construction.InitialMovingTreeWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkCoefficient

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_bulk {P : Type*} (b r : ℕ) (fallback : P)
    (small : List P) (hsmall : small.length = r + r)
    (bulk : Fin (b + b) → P) (i : Fin (b + b)) :
    initialRegularFromList b r fallback (small ++ List.ofFn bulk) ((), .inr i) = bulk i := by
  let y : MovingRegularSlot 0 (r + r) (b + b) → P :=
    fun j => Sum.elim (fun z => small.get (Fin.cast hsmall.symm z)) bulk j.2
  have hlist : (movingTemplateSlotList 0 (r + r) (b + b)).map y =
      small ++ List.ofFn bulk := by
    simp only [movingTemplateSlotList, movingTemplateSmall, bulkSlotLeaves,
      treeLeafTupleEquiv, Equiv.coe_fn_symm_mk, flattenMovingSlots, List.map_append,
      List.map_ofFn, Function.comp_def, y, movingTemplateBulk, Sum.elim_inl,
      ]
    congr 1
    exact (List.ofFn_congr hsmall small.get).symm.trans (List.ofFn_get small)
  have h := congrFun (initialRegularFromList_mapped b r fallback y) ((), .inr i)
  simpa only [hlist, y, Sum.elim_inr] using h

noncomputable def initialHalfBulkWeight {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (bulk : Fin (b + b) → P) : ℝ :=
  (initialLogSumWeight value cb (fun i : Fin b => bulk (i.castAdd b)) *
    initialLogSumWeight value cd sl) *
  (initialLogSumWeight value cb (fun i : Fin b => bulk (Fin.natAdd b i)) *
    initialLogSumWeight value cd sr)

theorem initialMovingRealWeight_list {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (small : List P) (hsmall : small.length = r + r) (bulk : Fin (b + b) → P) :
    initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback (small ++ List.ofFn bulk)) =
      initialHalfBulkWeight value b d cb cd sl sr bulk := by
  unfold initialMovingRealWeight initialHalfBulkWeight
  simp only [initialRegularFromList_bulk b r fallback small hsmall bulk]

end Ostmann

end OAI
