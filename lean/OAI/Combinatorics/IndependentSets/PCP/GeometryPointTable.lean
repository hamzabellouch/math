import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.GeometryExpr

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC
open scoped Classical
noncomputable section
variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def pointEquiv : StaticPoint L R n D ≃ Fin (staticCount L R n D) :=
  Fintype.equivFin (StaticPoint L R n D)

lemma nodeEquiv_val {nu nv : ℕ} (x : Node L R n D nu nv) :
    (nodeEquiv L R n D nu nv x).val=
      (pointEquiv L R n D x.2).val+staticCount L R n D*
        ((finFunctionFinEquiv x.1.2).val+nv^n*(finFunctionFinEquiv x.1.1).val) := rfl

def pointLookup (f : StaticPoint L R n D → ℕ) (x : Expr) : Expr :=
  Expr.finLookup (fun i => f ((pointEquiv L R n D).symm i)) x

lemma pointLookup_eval (f : StaticPoint L R n D → ℕ) (x : Expr) (s : List Bool) (a : ℕ → ℕ)
    (v : StaticPoint L R n D) (hv : x.eval s a=(pointEquiv L R n D v).val) :
    (pointLookup L R n D f x).eval s a=f v := by
  rw [pointLookup,Expr.finLookup_eval _ _ _ _ (pointEquiv L R n D v) hv,Equiv.symm_apply_apply]

lemma pointExpr_code (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (pointExpr L R n D x).eval t.bits a=
      (pointEquiv L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).2).val :=
  pointExpr_eval L R n D t x a i hi

end
end LargeIndependentSets.GeometryNames

end OAI
