import Mathlib.Algebra.Homology.ComplexShapeSigns

namespace OAI

namespace ArExplicit

instance cochainNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : Multiplicative ℕ) => (-1 : ℤˣ)^i.toAdd)
    (fun i j => pow_add (-1 : ℤˣ) i.toAdd j.toAdd)
  rel_add p q r (h : p+1=q) := by change (p+r)+1=q+r; omega
  add_rel p q r (h : p+1=q) := by change (r+p)+1=r+q; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ)^(p+1) = -(-1 : ℤˣ)^p
    exact (pow_succ (-1 : ℤˣ) p).trans (by simp)

end ArExplicit

end OAI
