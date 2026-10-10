import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas
import OAI.Geometry.NodalSets.Charts.SphereTangentTrace
import OAI.Geometry.NodalSets.Elliptic.CenteredRoundOperator

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma round_operator_ambient_restriction (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f) (p : Base) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (fun x : Base ↦ f x) p
      (extChartAt (𝓡 4) p p) =
    Δ f (p : AmbientBase) - fderiv ℝ (fderiv ℝ f) (p : AmbientBase)
      (p : AmbientBase) (p : AmbientBase) - 4 * fderiv ℝ f (p : AmbientBase) (p : AmbientBase) := by
  have hs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ f x) :=
    hf.contMDiff.comp (contMDiff_coe_sphere (n := 4))
  rw [centeredRoundOperator _ hs]
  simp_rw [sphere_restriction_chart_second f hf,
    (EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite]
  simp only [ite_true,one_mul,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have ht := sphere_tangent_trace f p
  rw [← ht]
  norm_num

end
end Yau.Target

end OAI
