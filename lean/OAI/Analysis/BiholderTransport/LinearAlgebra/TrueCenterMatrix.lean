import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.FixedJoinSpectrum
import OAI.Analysis.BiholderTransport.Coordinates.NormalLowerTaylorBound
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential
import OAI.Analysis.BiholderTransport.Contact.LocalCEMS
import OAI.Analysis.BiholderTransport.Volume.ExponentialJacobian
import OAI.Analysis.BiholderTransport.Regularity.PullbackDet

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteTrue (x:M):FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x):=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance tangentCompleteTrue (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normal_contact_matrix_symmetric {u:M → ℝ} {y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A) :
    ∀d e,inner ℝ ((normalHessianOperator y p+A) d) e=
      inner ℝ d ((normalHessianOperator y p+A) e) := by
  intro d e
  simp only [add_apply,inner_add_left,inner_add_right,
    inner_normalHessianOperator,hA.2.2.1]
  rw [←real_inner_comm d (normalHessianOperator y p e),inner_normalHessianOperator,
    normalHessian_symm hA.2.1 d e]

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normal_endpoint_derivative_injective {x y:M}
    {q:TangentSpace 𝓘(ℝ,Model n) x} (hq:q∈injectivityDomain x)
    {R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R q) (hR0:R q=0)
    (hRe:∀ᶠ v in 𝓝 q,riemannianExp y (R v)=riemannianExp x v) :
    Function.Injective (fderiv ℝ R q) := by
  have hy:y=riemannianExp x q:=by
    have H:=hRe.self_of_nhds
    simpa only [hR0,riemannianExp_zero] using H
  subst y
  have hi:Function.Injective (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
    (riemannianExp x) q):=(expJacobian_ne_zero_iff x q).mp
      (expJacobian_pos_of_injectivityDomain hq).ne'
  intro a b hab
  apply hi
  simpa only [←normal_endpoint_derivative_eq hR hR0 hRe] using hab

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma normal_scalar_chain_pullback {x y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    {l dd:ℝ} (hl:0<l)
    {q:TangentSpace 𝓘(ℝ,Model n) x}
    {B:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hg:∀d,l*inner ℝ p (B d)=-inner ℝ q d)
    (hS:∀d,inner ℝ (S d) d=dd*(inner ℝ p d)^2+l*inner ℝ (A d) d) :
    let V:=l • B.adjoint.comp ((normalHessianOperator y p+A).comp B)
    ∀d,inner ℝ (S (B d)) (B d)+normalHessian y (l • p) (B d) (B d)=
      inner ℝ (V d) d+
      (normalHessian y (l • p) (B d) (B d)-l*normalHessian y p (B d) (B d))+
      (dd/l^2)*(inner ℝ q d)^2 := by
  intro V d
  have hsquare:(inner ℝ p (B d))^2=(inner ℝ q d)^2/l^2:=by
    apply (eq_div_iff (pow_ne_zero _ hl.ne')).mpr
    have hh:=congrArg (fun z:ℝ=>z^2) (hg d)
    simp only [mul_pow,neg_sq] at hh
    simpa only [mul_comm] using hh
  dsimp only [V]
  rw [hS]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left,
    add_apply,inner_add_left,inner_normalHessianOperator]
  rw [hsquare]
  ring

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma true_center_matrix {u:M → ℝ} {x y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    {q:TangentSpace 𝓘(ℝ,Model n) x} (hq:q∈injectivityDomain x)
    (hxy:riemannianExp x q=y) {l:ℝ} (hl:0<l) (hl1:l<1)
    (hyx:riemannianExp y (l • p)=x) {φ:ℝ → ℝ}
    (hφ:ContDiffAt ℝ 2 φ (cTransform u y)) (hφd:deriv φ (cTransform u y)=l) :
    ∃R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
    ∃s:TangentSpace 𝓘(ℝ,Model n) y,
    ∃S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ z in 𝓝 q,riemannianExp y (R z)=riemannianExp x z) ∧
      (∀d e,inner ℝ (S d) e=inner ℝ d (S e)) ∧
      HasQuadraticExpansion (fun h=>φ (cTransform u (riemannianExp y h))) s S ∧
      let B:=fderiv ℝ R q
      let V:=l • B.adjoint.comp ((normalHessianOperator y p+A).comp B)
      (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
      V.det=l^n*(expJacobian x q)^2*(normalHessianOperator y p+A).det ∧
      ∀d,inner ℝ (S (B d)) (B d)+normalHessian y (l • p) (B d) (B d)=
        inner ℝ (V d) d+
        (normalHessian y (l • p) (B d) (B d)-l*normalHessian y p (B d) (B d))+
        (iteratedDeriv 2 φ (cTransform u y)/l^2)*(inner ℝ q d)^2 := by
  subst y
  let y:=riemannianExp x q
  obtain ⟨R,hR,hR0,hRe⟩:=exists_normal_endpoint_coordinates x q
  let B:=fderiv ℝ R q
  have hBd:DifferentiableAt ℝ R q:=hR.differentiableAt (by simp)
  have hBi:Function.Injective B:=normal_endpoint_derivative_injective hq hBd hR0 hRe
  have hWs:=normal_contact_matrix_symmetric hA
  have hdet:=det_positive_hessian_pullback (B:=B) (W:=normalHessianOperator y p+A) (l:=l)
    ((tangent_finrank x).trans (tangent_finrank y).symm) hBi hWs hp hl
  have hscalar:=quadratic_expansion_scalar_formula (φ:=φ) hA.2.2.2 hA.2.2.1
    (by simpa only [riemannianExp_zero] using hφ)
  obtain ⟨s,S,hS,hSe,hSf⟩:=hscalar
  refine ⟨R,s,S,hR,hR0,hRe,hS,hSe,hdet.1,?_,?_⟩
  · rw [hdet.2,tangent_finrank x]
    rw [expJacobian_eq_normal_endpoint hBd hR0 hRe]
  · apply normal_scalar_chain_pullback hl
    · intro d
      have hpr:l • p∈injectivityDomain y:=contracted_minimizer_mem_injectivityDomain
        (injectivityDomain_subset_minimizingVectors y hA.2.1) hl hl1
      simpa only [real_inner_smul_left] using
        reverse_normal_pairing hpr hq hyx hBd hR0 hRe d
    · simpa only [riemannianExp_zero,hφd] using hSf
end TrueCenterMatrix
end WeakMTWTransport

end
end

end OAI
