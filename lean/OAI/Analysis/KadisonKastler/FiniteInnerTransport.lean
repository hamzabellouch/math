import OAI.Analysis.KadisonKastler.FiniteOrderAveraging
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Transport of finite inner averages under inner automorphisms -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- Transport all averaging unitaries by a star automorphism. -/
def map (A : FiniteInnerAverage M) (f : Algebra M ≃⋆ₐ[ℂ] Algebra M) :
    FiniteInnerAverage M where
  Index := A.Index
  fintype := A.fintype
  nonempty := A.nonempty
  unitary i := Unitary.map (StarMonoidHom.ofClass f) (A.unitary i)

theorem map_algebraApply (A : FiniteInnerAverage M)
    (f : Algebra M ≃⋆ₐ[ℂ] Algebra M) (x : Algebra M) :
    (A.map f).algebraApply (f x) = f (A.algebraApply x) := by
  let L : Algebra M →ₗ[ℂ] Algebra M := f.toAlgEquiv.toLinearMap
  change (Fintype.card A.Index : ℂ)⁻¹ •
      (∑ i, f (A.unitary i) * f x * star (f (A.unitary i))) =
    L ((Fintype.card A.Index : ℂ)⁻¹ •
      (∑ i, (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M)))
  rw [L.map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change f (A.unitary i) * f x * star (f (A.unitary i)) =
    f ((A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M))
  rw [map_mul, map_mul]
  congr 1
  exact (f.map_star' _).symm

/-- Inner transport preserves the distance of the averaged element to a scalar. -/
theorem norm_map_inner_sub_scalar (A : FiniteInnerAverage M)
    (u : _root_.unitary (Algebra M)) (x : Algebra M) (z : ℂ) :
    ‖((A.map (Unitary.conjStarAlgAut ℂ (Algebra M) u)).algebraApply
        (Unitary.conjStarAlgAut ℂ (Algebra M) u x)).val - z • (1 : H →L[ℂ] H)‖ =
      ‖(A.algebraApply x).val - z • (1 : H →L[ℂ] H)‖ := by
  rw [map_algebraApply]
  have he : (Unitary.conjStarAlgAut ℂ (Algebra M) u (A.algebraApply x)).val -
      z • (1 : H →L[ℂ] H) =
      unitaryConj (ambientAlgebraUnitary u)
        ((A.algebraApply x).val - z • (1 : H →L[ℂ] H)) := by
    rw [unitaryConj_sub]
    congr 1
    symm
    change (u.val.val * (z • 1)) * star u.val.val = z • 1
    rw [mul_smul_comm, mul_one, smul_mul_assoc]
    have hu := congrArg Subtype.val (Unitary.mul_star_self_of_mem u.property)
    change u.val.val * star u.val.val = 1 at hu
    rw [hu]
  rw [he, norm_unitaryConj]

end FiniteInnerAverage

end

end KadisonKastler

end OAI
