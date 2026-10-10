import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartTrueMatrix
import OAI.Analysis.BiholderTransport.LinearAlgebra.TrueCenterMatrix
import OAI.Analysis.BiholderTransport.Calculus.TrueCenterGradient

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartTrueCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance chartTrueFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma chart_true_center_matrix {u:M → ℝ} {a c y:M} {b q:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    {l:ℝ} (hl:0<l) (hl1:l<1)
    (hpx:riemannianExp y (l • p)=(extChartAt 𝓘(ℝ,Model n) a).symm b)
    {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (cTransform u y))
    (hφd:deriv φ (cTransform u y)=l)
    {s:Model n} {S:Model n →L[ℝ] Model n}
    (hS:∀d e,inner ℝ (S d) e=inner ℝ d (S e))
    (hSe:HasQuadraticExpansion (fun h=>φ (cTransform u
      ((extChartAt 𝓘(ℝ,Model n) c).symm (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S) :
    ∃ R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) →
      TangentSpace 𝓘(ℝ,Model n) y,
    ∃ V:Model n →L[ℝ] Model n,
      DifferentiableAt ℝ R (chartFiberInverse a b q) ∧ R (chartFiberInverse a b q)=0 ∧
      (∀ᶠ z in 𝓝 (chartFiberInverse a b q),riemannianExp y (R z)=
        riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) z) ∧
      (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
      (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
      V.det=(chartFiberInverse a b).toLinearMap.normDet^2*l^n*
        (expJacobian ((extChartAt 𝓘(ℝ,Model n) a).symm b) (chartFiberInverse a b q))^2*
        (normalHessianOperator y p+A).det ∧
      ∀d,chartJetMatrix a c b q (innerSL ℝ s) ((innerSL ℝ).comp S) d d=
        inner ℝ (V d) d+
        (normalHessian y (l • p)
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))-
         l*normalHessian y p
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
          (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*
          (inner ℝ (chartFiberInverse a b q) (chartFiberInverse a b d))^2 := by
  let x: M := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let B:=chartFiberInverse a b
  have he:riemannianExp x (B q)=y:=by
    simpa only [movingPrefix_eq hb,one_smul,x,B,chartFiberInverse] using hy
  obtain ⟨R,r,T,hR,hR0,hRe,hT,hTe,hV,hVdet,hmat⟩:=
    true_center_matrix hA hp hq he hl hl1 hpx hφ hφd
  let C:=fderiv ℝ R (B q)
  let W:=normalHessianOperator y p+A
  let V0:=l • C.adjoint.comp (W.comp C)
  let V:=B.adjoint.comp (V0.comp B)
  have hWs:=normal_contact_matrix_symmetric hA
  have hV0s:∀d e,inner ℝ (V0 d) e=inner ℝ d (V0 e):=by
    intro d e
    simp only [V0,smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    rw [hWs]
  have hB:Function.Injective B:=by
    exact chartFiberInverse_injective hb
  have hdim:Module.finrank ℝ (Model n)=Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x):=by
    rw [tangent_finrank]
    exact finrank_euclideanSpace_fin
  have hP:=det_positive_hessian_pullback (B:=B) (W:=V0) hdim hB hV0s hV (show (0:ℝ)<1 by norm_num)
  simp only [one_smul,one_pow,one_mul] at hP
  have hr:r=l • p:=quadratic_scalar_gradient hA.2.2.2
    (by simpa only [riemannianExp_zero,hφd] using (hφ.differentiableAt (by norm_num)).hasDerivAt) hTe
  rw [hr] at hTe
  have hpr:l • p∈injectivityDomain y:=contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors y hA.2.1) hl hl1
  have hid:=chartJetMatrix_normal_identity (f:=fun z=>φ (cTransform u z)) hb hq hy hc hpr hpx hTe hS hSe
    (hR.differentiableAt (by simp)) hR0 hRe
  refine ⟨R,V,hR.differentiableAt (by simp),hR0,hRe,?_,hP.1,?_,?_⟩
  · intro d e
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hV0s]
  · change V.det=_
    rw [hP.2]
    change B.toLinearMap.normDet^2*V0.det=_
    rw [hVdet]
    ring
  · intro d
    rw [hid d,hmat (B d)]
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    rfl
end ChartTrueCenter
end WeakMTWTransport

end
end

end OAI
