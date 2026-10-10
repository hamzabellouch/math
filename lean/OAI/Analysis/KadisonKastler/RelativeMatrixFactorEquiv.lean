import OAI.Analysis.KadisonKastler.FactorIsomorphism
import OAI.Analysis.KadisonKastler.ProjectionMatrixInsertion

namespace OAI

/-! # A finite matrix commutant in a type III factor

An isometry onto one diagonal matrix corner identifies the ambient algebra
with the matrix commutant. This also transports the type III predicate.
-/

noncomputable section

namespace Generator.MatrixUnitSystem

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  (E : Generator.MatrixUnitSystem ι A) (o : ι) (v : A)
  (hv : star v * v = 1) (hp : v * star v = E.entry o o)

include hv hp

omit [StarModule ℂ A] in
private theorem corner_isometry_left : E.entry o o * v = v := by
  rw [← hp,mul_assoc,hv,mul_one]

omit [StarModule ℂ A] in
private theorem corner_isometry_right : star v * E.entry o o = star v := by
  rw [← hp,← mul_assoc,hv,one_mul]

def isometricCommutantEquiv : A ≃⋆ₐ[ℂ] E.commutant where
  toFun x := ⟨E.amplify o (v*x*star v),E.amplify_mem o _⟩
  invFun y := star v*y.val*v
  left_inv x := by
    change star v * E.amplify o (v*x*star v) * v = x
    calc
      _ = star v * (E.entry o o * E.amplify o (v*x*star v) * E.entry o o) * v := by
        symm
        calc
          _ = ((star v * E.entry o o) * E.amplify o (v*x*star v)) *
              (E.entry o o * v) := by simp only [mul_assoc]
          _ = _ := by rw [E.corner_isometry_right o v hv hp,E.corner_isometry_left o v hv hp]
      _ = star v * (E.entry o o * (v*x*star v) * E.entry o o) * v := by
        rw [E.amplify_corner]
      _ = x := by
        calc
          _ = (star v * E.entry o o) * (v*x*star v) * (E.entry o o * v) := by
            simp only [mul_assoc]
          _ = star v * (v*x*star v) * v := by
            rw [E.corner_isometry_right o v hv hp,E.corner_isometry_left o v hv hp]
          _ = (star v*v)*x*(star v*v) := by simp only [mul_assoc]
          _ = x := by rw [hv,one_mul,mul_one]
  right_inv y := by
    apply Subtype.ext
    change E.amplify o (v*(star v*y.val*v)*star v) = y.val
    have he : v*(star v*y.val*v)*star v = E.entry o o*y.val := by
      calc
        _ = E.entry o o*y.val*E.entry o o := by simp only [← hp,mul_assoc]
        _ = E.entry o o*(E.entry o o*y.val) := by
          rw [mul_assoc,← (y.property o o).eq]
        _ = E.entry o o*y.val := by
          rw [← mul_assoc,E.mul_entry,ite_eq_left rfl]
    rw [he,E.amplify_compression o y.val y.property]
  map_mul' x y := by
    apply Subtype.ext
    change E.amplify o (v*(x*y)*star v) =
      E.amplify o (v*x*star v)*E.amplify o (v*y*star v)
    rw [E.amplify_mul]
    congr 1
    symm
    calc
      _ = (v*x*star v)*((E.entry o o*v)*y*star v) := by simp only [mul_assoc]
      _ = v*x*(star v*v)*y*star v := by
        rw [E.corner_isometry_left o v hv hp]
        simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one]; simp only [mul_assoc]
  map_add' x y := by
    apply Subtype.ext
    change E.amplify o (v*(x+y)*star v) =
      E.amplify o (v*x*star v) + E.amplify o (v*y*star v)
    simp only [amplify,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' c x := by
    apply Subtype.ext
    change E.amplify o (v*(c • x)*star v) = c • E.amplify o (v*x*star v)
    simp only [amplify,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]
  map_star' x := by
    apply Subtype.ext
    change E.amplify o (v*star x*star v) = star (E.amplify o (v*x*star v))
    rw [E.amplify_star]
    simp only [star_mul,star_star,mul_assoc]

end Generator.MatrixUnitSystem

namespace KadisonKastler

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_relative_matrix_equiv (hM : TypeIIIFactor M)
    (E : FiniteMatrixStage M) :
    Nonempty (Algebra M ≃⋆ₐ[ℂ] Algebra E.units.relativeVonNeumann) := by
  let : Nontrivial (Algebra M) := nontrivial_of_ne (1 : Algebra M) 0
    (fun h => hM.nonzero (congrArg Subtype.val h))
  let o : Fin E.size := ⟨0,E.positive⟩
  have hp : IsStarProjection (E.units.entry o o) := ⟨by
    change E.units.entry o o * E.units.entry o o = E.units.entry o o
    rw [E.units.mul_entry,ite_eq_left rfl],by rw [IsSelfAdjoint,E.units.star_entry]⟩
  obtain ⟨v,hv,hp⟩ := hM.exists_isometry_onto_projection (E.units.entry o o) hp
    (E.units.diagonal_ne_zero o)
  exact ⟨(E.units.isometricCommutantEquiv o v hv hp).trans E.units.relativeEquiv⟩

theorem TypeIIIFactor.relative_matrix (hM : TypeIIIFactor M)
    (E : FiniteMatrixStage M) : TypeIIIFactor E.units.relativeVonNeumann := by
  obtain ⟨e⟩ := hM.exists_relative_matrix_equiv E
  exact hM.of_starAlgEquiv e

end KadisonKastler

end

end OAI
