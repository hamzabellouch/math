import OAI.Geometry.Kahler.BaseCorrectionMoments

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def linearSubstitution (U : Base →ₗ[ℂ] Base) (i : Fin 2) : MvPolynomial (Fin 2) ℂ :=
  ∑ j : Fin 2, MvPolynomial.C (U (EuclideanSpace.single j 1) i)*MvPolynomial.X j

lemma linearSubstitution_eval (U : Base →ₗ[ℂ] Base) (z : Base) (i : Fin 2) :
    MvPolynomial.eval (fun j => z j) (linearSubstitution U i)=U z i := by
  simp only [linearSubstitution,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  conv_rhs => rw [base_eq_sum_single z,map_sum]
  simp only [map_smul,Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma polynomial_change_coords (U : Base ≃ₗᵢ[ℂ] Base) (P : MvPolynomial (Fin 2) ℂ) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, ∀ z : Base,
      MvPolynomial.eval (fun i => U z i) Q = MvPolynomial.eval (fun i => z i) P := by
  refine ⟨MvPolynomial.bind₁ (linearSubstitution U.symm.toLinearEquiv.toLinearMap) P,?_⟩
  intro z
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => U z i) _=_
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun j => U z j)
      (linearSubstitution U.symm.toLinearEquiv.toLinearMap i))=fun i => z i := by
    funext i
    change MvPolynomial.eval (fun j => U z j) _=z i
    rw [linearSubstitution_eval]
    simp
  rw [he]
  rfl

end PinchedHartogs.BaseConstruction

end

end OAI
