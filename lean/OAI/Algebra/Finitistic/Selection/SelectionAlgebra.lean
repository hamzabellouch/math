import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum
import OAI.Algebra.Finitistic.Selection.GroupSelection

namespace OAI
namespace LittleFinitistic

open MonoidAlgebra

abbrev SelectionRing := MonoidAlgebra ℂ Presentation.AuxiliaryGroup

noncomputable def algebraZ (q : ℤ) : SelectionRing := single (Presentation.z q) 1

@[simp] theorem algebraZ_square (q : ℤ) : algebraZ q * algebraZ q = 1 := by
  simp [algebraZ,single_mul_single,Presentation.z_involution]
  rfl

theorem algebraZ_central (q : ℤ) (a : SelectionRing) : Commute (algebraZ q) a :=
  MonoidAlgebra.single_commute (Presentation.z_central q) Commute.one_left a

noncomputable def selectionIdempotent (q : ℤ) : SelectionRing :=
  (1/2 : ℂ) • (1 + algebraZ q)

theorem selectionIdempotent_square (q : ℤ) :
    selectionIdempotent q * selectionIdempotent q = selectionIdempotent q := by
  have hz : (1 + algebraZ q)*(1 + algebraZ q) = (1+algebraZ q)+(1+algebraZ q) := by
    simp only [mul_add,add_mul,one_mul,mul_one,algebraZ_square]
    abel
  unfold selectionIdempotent
  rw [smul_mul_smul,hz,smul_add,← add_smul]
  norm_num

theorem selectionIdempotent_central (q : ℤ) (a : SelectionRing) :
    Commute (selectionIdempotent q) a := by
  show selectionIdempotent q * a = a * selectionIdempotent q
  unfold selectionIdempotent
  rw [smul_mul_assoc,mul_smul_comm]
  congr 1
  simp only [add_mul,mul_add,one_mul,mul_one,(algebraZ_central q a).eq]

noncomputable def selectionAutomorphism (k : ℤ) : SelectionRing ≃ₐ[ℂ] SelectionRing :=
  MonoidAlgebra.domCongr ℂ ℂ (Presentation.shiftAut k)

@[simp] theorem selectionAutomorphism_z (k q : ℤ) :
    selectionAutomorphism k (algebraZ q) = algebraZ (q+k) := by
  simp [selectionAutomorphism,algebraZ,Presentation.shiftAut_z]

@[simp] theorem selectionAutomorphism_idempotent (k q : ℤ) :
    selectionAutomorphism k (selectionIdempotent q) = selectionIdempotent (q+k) := by
  simp [selectionIdempotent]

end LittleFinitistic

end OAI
