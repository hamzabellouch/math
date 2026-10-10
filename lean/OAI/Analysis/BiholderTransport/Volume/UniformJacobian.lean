import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiberLog

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteUniformJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_mfderiv_zero_apply (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v=v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have heq : (fun t : ℝ => riemannianExp x (t • v))=
      (fun t : ℝ => (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :=
    funext (riemannianExp_smul x v)
  have hf : HasFDerivAt (fun t : ℝ => t • v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) 0 :=
    ((1 : ℝ →L[ℝ] ℝ).smulRight v).hasFDerivAt
  have H := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,V))
    (I'' := 𝓘(ℝ,Model n)) (0:ℝ)
    ((contMDiff_riemannianExp_fiber x (0 • v)).mdifferentiableAt (by simp))
    hf.differentiableAt.mdifferentiableAt (1:ℝ)
  have hv := spray_velocity_eq_mfderiv ((sprayFlow_curve
    (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).isMIntegralCurveAt (0:ℝ))
  simp only [Function.comp_def,mfderiv_eq_fderiv,hf.fderiv] at H
  rw [heq] at H
  rw [sprayFlow_zero] at hv
  have hz : (0:ℝ) • v=(0:V) := zero_smul ℝ v
  have h1 : ((1 : ℝ →L[ℝ] ℝ).smulRight v) (1:ℝ)=v := by simp
  erw [hz,h1] at H
  exact H.symm.trans hv

end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance tangentFiniteExpJac (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def expJacobian (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  (show TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p) from
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp (n := n) x) p).toLinearMap.normDet

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_nonneg (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    0≤expJacobian x p := LinearMap.normDet_nonneg _

lemma normal_endpoint_derivative_eq {x y : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v)
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ L p k=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) p k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  have H := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,W))
    (I'' := 𝓘(ℝ,Model n)) p
    ((contMDiff_riemannianExp_fiber y 0).mdifferentiableAt (by simp))
    hL.mdifferentiableAt hLp k
  erw [mfderiv_eq_fderiv,exp_mfderiv_zero_apply] at H
  have HC := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ,V)) (I' := 𝓘(ℝ,Model n))
    (show riemannianExp y ∘ L =ᶠ[𝓝 p] riemannianExp x from hLi)
  have HC' := congrArg (fun A => A k) HC
  exact H.symm.trans HC'

lemma expJacobian_eq_normal_endpoint {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hL : DifferentiableAt ℝ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) :
    expJacobian x p=(fderiv ℝ L p).toLinearMap.normDet := by
  unfold expJacobian
  apply congrArg LinearMap.normDet
  ext k
  exact (normal_endpoint_derivative_eq hL hLp hLi k).symm

lemma exists_normal_endpoint_coordinates (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      ContDiffAt ℝ ∞ L p ∧ L p=0 ∧
      (∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (L v)=riemannianExp x v) := by
  let y := riemannianExp x p
  obtain ⟨N,hN,hN0,hNi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) y)
  simp only [riemannianExp_zero] at hN hN0 hNi
  refine ⟨(fun v => N (riemannianExp x v)),?_,hN0,?_⟩
  · exact (hN.comp p (contMDiff_riemannianExp_fiber x p)).contDiffAt
  · exact (continuous_riemannianExp x).continuousAt.eventually hNi
end WeakMTWTransport

end

end OAI
