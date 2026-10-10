import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.LowerTaylorComposition
import OAI.Analysis.BiholderTransport.Regularity.OuterIntrinsicSecond
import OAI.Analysis.BiholderTransport.Coordinates.NormalEndpointInverse

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance otFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

local instance otComplete (x:M):CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x):=
  FiniteDimensional.complete ℝ _

lemma WeakMTW.exists_uniform_outer_true_matrix
    (hmtw:WeakMTW (n:=n) (M:=M)) {lam cap:ℝ} (hlam:0<lam) (hcap:0≤cap) :
    ∃K>0,∀ (x y:M) (p:TangentSpace 𝓘(ℝ,Model n) x)
      (r:TangentSpace 𝓘(ℝ,Model n) y) (G:M×M → ℝ) (l:ℝ),
      riemannianExp x p=y → riemannianExp y r=x → r∈minimizingVectors y →
      Function.Injective (fderiv ℝ (fun v=>extChartAt 𝓘(ℝ,Model n)
        (riemannianExp x p) (riemannianExp x v)) p) →
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (y,x) →
      (∀ᶠ q in 𝓝 p,G (riemannianExp x q,x)=‖q‖^2/2) →
      (∀ᶠ z in 𝓝 (⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M),z.2∈injectivityDomain z.1 →
        (fun q:M×M=>cost q.1 q.2)=ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) → 1<l →
      ∀ (x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)) (φ:ℝ → ℝ),
      uv∈densityDualClass (metricVolume n) lam cap x0 → StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.2 y) → HasDerivAt φ l (uv.2 y) → iteratedDeriv 2 φ (uv.2 y)≤0 →
      ∀ B:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ,
      (∀d e,B d e=B e d) → (∀d,0≤B d d) →
      HasLowerSecondTaylor (fun d=>φ (uv.2 (riemannianExp x (p+d)))+‖p+d‖^2/2) 0 B →
      ∃ (C:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y)
        (V:TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x),
        Function.Injective C ∧ C.toLinearMap.normDet=expJacobian (n:=n) x p ∧
        (∀d,inner ℝ r (C d)=-inner ℝ p d) ∧
        (∀d e,inner ℝ (V d) e=inner ℝ d (V e)) ∧
        (∀d,d≠0 → 0 < inner ℝ (V d) d) ∧
        (∀d,inner ℝ (V d) d=B d d+(l*hessianValue y (l⁻¹ • r) (C d)-
          fderiv ℝ (fderiv ℝ (fun w=>G (riemannianExp y w,x))) 0 (C d) (C d))-
          (iteratedDeriv 2 φ (uv.2 y)/l^2)*(inner ℝ p d)^2) ∧
        expJacobian (n:=n) y (l⁻¹ • r)*V.det≤l^n*K*(expJacobian (n:=n) x p)^2 := by
  obtain ⟨K,hK,HK⟩:=hmtw.exists_uniform_outer_normal_det_bound_second hlam hcap
  refine ⟨K,hK,?_⟩
  intro x y p r G l hxy hyx hr hp hG hact hagree hl x0 uv φ huv hmono hφ hd hconc B hBs hB hjet
  subst y
  let y:=riemannianExp x p
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let F:=TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨e,C,he,he0,hei,hCI,hCJ,hJC,hCd⟩:=exists_normal_endpoint_inverse hp
  let J:F →L[ℝ] E:=fderiv ℝ e 0
  let H:=pullBilinear B J
  have hHs:∀d e,H d e=H e d:=by intro d e; exact hBs (J d) (J e)
  have hHp:∀d,0≤H d d:=fun d=>hB (J d)
  have hJcomp (d:E):J (C d)=d:=congrArg (fun A:E →L[ℝ] E=>A d) hJC
  have hjet2:HasLowerSecondTaylor
      (fun w:F=>φ (uv.2 (riemannianExp y w))+G (riemannianExp y w,x)) 0 H:=by
    have ha:HasFDerivAt (fun w:F=>e w-p) J 0:=
      (he.differentiableAt (by simp)).hasFDerivAt.sub_const p
    have Z:=HasLowerSecondTaylor.comp_stationary hjet ha (by rw [he0,sub_self])
    have ha':=he.continuousAt.eventually (show ∀ᶠ q in 𝓝 (e 0),G (riemannianExp x q,x)=‖q‖^2/2
      from by rw [he0]; exact hact)
    have hEq:(fun w:F=>φ (uv.2 (riemannianExp x (p+(e w-p))))+‖p+(e w-p)‖^2/2) =ᶠ[𝓝 0]
        (fun w:F=>φ (uv.2 (riemannianExp y w))+G (riemannianExp y w,x)):=by
      filter_upwards [hei,ha'] with w hw ha
      have hh:p+(e w-p)=e w:=by abel
      rw [hh,←hw,ha]
    exact Z.mono hEq.eq_of_nhds hEq.le
  have hG':ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (y,riemannianExp y r):=by rw [hyx]; exact hG
  obtain ⟨N,hNs,hNp,hNd,hNdet⟩:=HK y r G l hr hG' hagree hl x0 uv φ huv hmono hφ hd hconc H hHs hHp
    (by simpa only [y,hyx] using hjet2)
  have hcD:HasFDerivAt (fun w:F=>G (riemannianExp y w,x)) (innerSL ℝ (-r)) 0:=by
    have HH:=cost_branch_normal_jets (r:=r) (T:=(1:ℝ)) (by norm_num)
      (by simpa only [one_smul] using hG') (by simpa only [one_smul] using hagree)
      (fun s hs=>contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
    simpa only [one_smul,hyx] using HH.2.1
  have heq:(fun w:F=>G (riemannianExp y w,x)) =ᶠ[𝓝 0] (fun w:F=>‖e w‖^2/2):=by
    have ha':=he.continuousAt.eventually (show ∀ᶠ q in 𝓝 (e 0),G (riemannianExp x q,x)=‖q‖^2/2
      from by rw [he0]; exact hact)
    filter_upwards [hei,ha'] with w hw ha
    rw [←hw,ha]
  have henergy:HasFDerivAt (fun v:E=>‖v‖^2/2) (innerSL ℝ p) p:=by
    convert! ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_mul (1/2:ℝ)) using 1
    · ext v; ring
    · ext v; simp only [smul_apply,smul_eq_mul]; ring
  have henergy2:HasFDerivAt (fun w:F=>‖e w‖^2/2) ((innerSL ℝ p).comp J) 0:=
    (show HasFDerivAt (fun v:E=>‖v‖^2/2) (innerSL ℝ p) (e 0) from by rw [he0]; exact henergy).comp
      0 (he.differentiableAt (by simp)).hasFDerivAt
  have hpair:∀d,inner ℝ r (C d)=-inner ℝ p d:=by
    intro d
    have HH:innerSL ℝ (-r)=(innerSL ℝ p).comp J:=
      (hcD.congr_of_eventuallyEq heq.symm).unique henergy2
    have hh:=congrArg (fun A:F →L[ℝ] ℝ=>A (C d)) HH
    simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,inner_neg_left,hJcomp] at hh
    linarith only [hh]
  let V:=C.adjoint.comp (N.comp C)
  have hVs:∀d e,inner ℝ (V d) e=inner ℝ d (V e):=by
    intro d e
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hNs]
  have hpos:=det_positive_hessian_pullback (B:=C) (W:=N)
    ((tangent_finrank x).trans (tangent_finrank y).symm) hCI hNs hNp (l:=1) (by norm_num)
  simp only [one_smul,one_pow,one_mul] at hpos
  refine ⟨C,V,hCI,hCd.symm,hpair,hVs,hpos.1,?_,?_⟩
  · intro d
    simp only [V,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
    rw [hNd,hyx]
    change B (J (C d)) (J (C d))+_ -_ =_
    rw [hJcomp,hpair,neg_sq]
  · have HV:V.det=expJacobian (n:=n) x p^2*N.det:=by rw [hpos.2,←hCd]
    rw [HV]
    nlinarith only [mul_le_mul_of_nonneg_right hNdet (sq_nonneg (expJacobian (n:=n) x p))]
end OuterTrueMatrix
end WeakMTWTransport

end
end

end OAI
