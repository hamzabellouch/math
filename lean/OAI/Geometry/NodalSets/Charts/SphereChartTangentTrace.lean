import OAI.Geometry.NodalSets.Charts.SphereChartConformal
import OAI.Geometry.NodalSets.Charts.SphereTangentTrace

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChartDerivative_normal (p : Base) (y v : BaseModel) :
    ⟪((extChartAt (𝓡 4) p).symm y : AmbientBase), sphereChartDerivative p y v⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm]
  exact sphere_derivative_radial_orthogonal ((extChartAt (𝓡 4) p).symm y)
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y v)

def sphereConformalFrame (p : Base) (y : BaseModel) : Fin 4 ⊕ Fin 1 → AmbientBase :=
  Sum.elim (fun i ↦ ((‖y‖^2+4)/4) •
    sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
    (fun _ ↦ (extChartAt (𝓡 4) p).symm y)

lemma sphereConformalFrame_orthonormal (p : Base) (y : BaseModel) :
    Orthonormal ℝ (sphereConformalFrame p y) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [sphereConformalFrame,Sum.elim_inl,real_inner_smul_left,
      real_inner_smul_right,sphereChartDerivative_conformal]
    rw [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite]
    have hd : ‖y‖^2+4 ≠ 0 := by positivity
    split_ifs <;> simp_all
    field_simp
  · change ⟪((‖y‖^2+4)/4) • sphereChartDerivative p y _,
      ((extChartAt (𝓡 4) p).symm y : AmbientBase)⟫ = 0
    rw [real_inner_smul_left,real_inner_comm,sphereChartDerivative_normal,mul_zero]
  · simp only [sphereConformalFrame,Sum.elim_inl,Sum.elim_inr,real_inner_smul_right,
      sphereChartDerivative_normal,mul_zero,Sum.inr_ne_inl,ite_false]
  · simp [sphereConformalFrame,Subsingleton.elim i j]

def sphereConformalBasis (p : Base) (y : BaseModel) :
    OrthonormalBasis (Fin 4 ⊕ Fin 1) ℝ AmbientBase :=
  OrthonormalBasis.mk (sphereConformalFrame_orthonormal p y)
    ((sphereConformalFrame_orthonormal p y).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [AmbientBase])).ge

lemma sphereConformalBasis_apply (p : Base) (y : BaseModel) (i : Fin 4 ⊕ Fin 1) :
    sphereConformalBasis p y i = sphereConformalFrame p y i := by
  simp [sphereConformalBasis]

lemma sphere_chart_tangent_trace (f : AmbientBase → ℝ) (p : Base) (y : BaseModel) :
    (∑ i, fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))) =
    (4/(‖y‖^2+4))^2 *
      (Δ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
       fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)) := by
  have h := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (sphereConformalBasis p y)) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
  simp only [Fintype.sum_sum_type,iteratedFDeriv_two_apply,sphereConformalBasis_apply,
    sphereConformalFrame,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one,map_smul,smul_apply,smul_eq_mul,
    Fin.sum_univ_one,← mul_assoc,← Finset.mul_sum] at h
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  rw [h]
  field_simp
  ring

end
end Yau.Target

end OAI
