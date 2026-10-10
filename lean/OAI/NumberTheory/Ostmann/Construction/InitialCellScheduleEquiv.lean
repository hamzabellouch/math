import Mathlib.Data.List.OfFn
import OAI.NumberTheory.Ostmann.Construction.InitialCellSchedule

namespace OAI

/-! # An exact index bijection for the two original cell lists -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallCell_ofFn (top : ℕ) (cs : List ℕ) :
    List.ofFn (scheduledSmallCell top cs) = scheduledSmallCellList top cs := by
  induction cs with
  | nil => exact List.ofFn_const 6 top
  | cons c cs ih =>
    change List.ofFn (Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs)) = _
    rw [List.ofFn_fin_append, List.ofFn_const, ih]
    rfl

theorem ofFn_perm_index_equiv {n m : ℕ} (f : Fin n → ℕ) (g : Fin m → ℕ)
    (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ e : Fin n ≃ Fin m, ∀ i, g (e i) = f i := by
  let E : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    ⟨h.idxBij, h.symm.idxBij, fun _ => h.idxBij_symm_idxBij,
      fun _ => h.idxBij_idxBij_symm⟩
  let e := ((finCongr (List.length_ofFn (f := f)).symm).trans E).trans
    (finCongr (List.length_ofFn (f := g)))
  refine ⟨e, ?_⟩
  intro i
  have hi := h.getElem_idxBij_eq_getElem ((finCongr (List.length_ofFn (f := f)).symm) i)
  simp only [List.getElem_ofFn] at hi
  convert hi using 1 <;> congr 1

theorem initialCellSchedule_index_equiv (top : ℕ) (cs : List ℕ) :
    let cells := initialSmallCellList top cs
    ∃ e : Fin (cells.length + cells.length) ≃ Fin (scheduledSmallLength cs),
      ∀ i, scheduledSmallCell top cs (e i) = Fin.append cells.get cells.get i := by
  intro cells
  apply ofFn_perm_index_equiv
  rw [List.ofFn_fin_append]
  simp only [List.ofFn_get, scheduledSmallCell_ofFn]
  exact initialSmallCellList_schedule_perm top cs

end Ostmann

end OAI
