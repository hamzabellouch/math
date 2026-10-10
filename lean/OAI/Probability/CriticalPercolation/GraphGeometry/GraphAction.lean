import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[ext] lemma Aut.ext {f g : G.Aut} (hv : f.vertex=g.vertex) (he : f.edge=g.edge) : f=g := by
  cases f
  cases g
  cases hv
  cases he
  rfl

instance : Group G.Aut where
  one := ⟨Equiv.refl V,Equiv.refl E,by intro e; simp⟩
  mul f g := Aut.trans G g f
  inv f := Aut.symm G f
  mul_assoc f g h := by apply Aut.ext G <;> rfl
  one_mul f := by apply Aut.ext G <;> rfl
  mul_one f := by apply Aut.ext G <;> rfl
  inv_mul_cancel f := by
    apply Aut.ext G <;> apply Equiv.ext <;> intro x <;>
      exact Equiv.symm_apply_apply _ x

instance : MulAction G.Aut V where
  smul f x := f.vertex x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma Aut.smul_vertex (f : G.Aut) (x : V) : f • x=f.vertex x := rfl

end CriticalPercolation.BondGraph
end
end
end

end OAI
