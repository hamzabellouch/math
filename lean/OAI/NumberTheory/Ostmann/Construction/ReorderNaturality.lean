import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicSlots
import OAI.NumberTheory.Ostmann.Construction.ReorderNaturalityIndex

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicSlots
open Construction Characters.RationalHistory OccurrencePermutation

theorem reorder_eq_of_get {ι : Type*} {xs ys : List SmallSlot}
    (h : xs.Perm ys) (hy : ys.Nodup) (e : Fin xs.length ≃ Fin ys.length)
    (he : ∀i,ys.get (e i)=xs.get i) (f : Fin xs.length→Expr ι) :
    reorder h f=fun i => f (e.symm i) := by
  unfold reorder
  rw [indexEquiv_eq_of_get h hy e he]

theorem reorder_naturality {ι κ : Type*} {xs ys xs' ys' : List SmallSlot}
    (h : xs.Perm ys) (h' : xs'.Perm ys') (hy' : ys'.Nodup)
    (ex : Fin xs.length ≃ Fin xs'.length) (ey : Fin ys.length ≃ Fin ys'.length)
    (hmatch : ∀i j,ys.get j=xs.get i → ys'.get (ey j)=xs'.get (ex i))
    (f : Fin xs.length→Expr ι) (f' : Fin xs'.length→Expr κ) (R : Expr ι→Expr κ)
    (hf : ∀i,f' (ex i)=R (f i)) (j : Fin ys.length) :
    reorder h' f' (ey j)=R (reorder h f j) :=
  pullback_naturality h h' hy' ex ey hmatch f f' R hf j

end Ostmann.Arithmetic.HistorySymbolicSlots

end

end OAI
