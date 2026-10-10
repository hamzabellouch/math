import OAI.Geometry.NodalSets.Charts.FixedChartRoundOperator
import OAI.Geometry.NodalSets.Charts.SphereAmbientLaplacian
import OAI.Geometry.NodalSets.Charts.SphereChartTangentTrace
import OAI.Geometry.NodalSets.Charts.SphereRestrictionArbitraryHessian

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphere_coordinate_linear_sum (L : BaseModel →L[ℝ] ℝ) (y : BaseModel) :
    ∑ i, y i * L (EuclideanSpace.basisFun (Fin 4) ℝ i) = L y := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr y)
  simpa using h

lemma sphere_restriction_second_trace_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y : BaseModel) :
    (∑ i, fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) y
      (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
    (∑ i, fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))) +
    (4/(‖y‖^2+4)) *
      fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y y -
    (4*(4/(‖y‖^2+4))^2) *
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  simp only [sphere_restriction_chart_second_at f hf,sphereChart_second_at,
    map_sub,map_add,map_smul,smul_eq_mul]
  have hi (i : Fin 4) : ⟪y,EuclideanSpace.basisFun (Fin 4) ℝ i⟫ = y i := by
    rw [real_inner_comm,EuclideanSpace.basisFun_inner]
  simp only [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite,ite_true,hi,one_mul,mul_one]
  simp_rw [← sphere_restriction_chart_first_at f hf]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hs := sphere_coordinate_linear_sum
    (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y) y
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at *
  rw [hs]
  ring

theorem fixed_chart_round_operator_ambient_restriction (f : AmbientBase → ℝ)
    (hf : ContDiff ℝ ∞ f) (p : Base) (y : BaseModel) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (fun x : Base ↦ f x) p y =
      Δ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
      fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
      4 * fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  have hfm : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ f x) :=
    hf.contMDiff.comp (contMDiff_coe_sphere (n := 4))
  rw [fixedChartRoundOperator _ hfm,sphere_restriction_second_trace_at f hf,
    sphere_chart_tangent_trace,sphere_coordinate_linear_sum]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

end
end Yau.Target

end OAI
