import Mathlib
import OAI.Analysis.BiholderTransport.Volume.ChartJacobianBounds
import OAI.Analysis.BiholderTransport.Regularity.MixedIntrinsic
import OAI.Analysis.BiholderTransport.LinearAlgebra.NormDetAdjoint

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MixedDetIntrinsic
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance midFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] in
lemma mixed_intrinsic_det {x a b:M} {p:TangentSpace 𝓘(ℝ,Model n) x}
    (hx:x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp:p∈injectivityDomain x)
    (hy:riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    chartJacobian (n:=n) a x *
      |(mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
        (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))).det| *
      (chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p)=1 := by
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let T:=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n:=n) x) 0
  let S:=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n:=n) x) p
  let B:=mixedCostOperator a b (extChartAt 𝓘(ℝ,Model n) a x)
    (extChartAt 𝓘(ℝ,Model n) b (riemannianExp x p))
  have hT:T.toLinearMap.normDet=chartJacobian (n:=n) a x:=normDet_chart_exp_zero _ _ hx
  have hS:S.toLinearMap.normDet=chartJacobian (n:=n) b (riemannianExp x p)*expJacobian (n:=n) x p:=
    normDet_chart_exp _ _ _ hy
  have hTa:T.adjoint.toLinearMap.normDet=T.toLinearMap.normDet:=
    normDet_adjoint_of_pos T rfl (hT.symm ▸ chartJacobian_pos hx)
  have H:=congrArg (fun A:E →L[ℝ] E=>A.toLinearMap.normDet) (mixed_intrinsic_factor hx hp hy)
  change (T.adjoint.comp (B.comp S)).toLinearMap.normDet=(LinearMap.id:E →ₗ[ℝ] E).normDet at H
  rw [normDet_comp_three S B T.adjoint rfl rfl,LinearMap.normDet_id,hTa,hT,hS,
    LinearMap.normDet_eq_abs_det] at H
  exact H

end MixedDetIntrinsic
end WeakMTWTransport

end
end

end OAI
