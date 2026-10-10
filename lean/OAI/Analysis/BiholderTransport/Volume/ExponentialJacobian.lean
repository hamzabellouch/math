import Mathlib
import OAI.Analysis.BiholderTransport.Volume.UniformJacobian

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExponentialJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteExponentialJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma mfderiv_exp_zero_norm (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp (n := n) x) 0 v‖=‖v‖ := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v⟩
  have hline : HasFDerivAt (fun t : ℝ => t • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) 0 := (hasFDerivAt_id 0).smul_const v
  have he := ((contMDiff_riemannianExp_fiber x ((0:ℝ) • v)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := he.comp 0 hline.hasMFDerivAt
  have hs := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt 0)
  have hfun : (fun t : ℝ => riemannianExp (n := n) x (t • v))=(fun t : ℝ => (sprayFlow t z).1) :=
    funext (riemannianExp_smul x v)
  have hsN : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n)
      (fun t : ℝ => (sprayFlow t z).1) 0 1‖=‖v‖ := by
    rw [hs.mfderiv]
    change ‖(1 : ℝ) • (sprayFlow 0 z).2‖ = ‖v‖
    simpa only [one_smul] using sprayFlow_speed 0 z
  have hnorm := (congrArg (fun f : ℝ → M =>
    ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) f 0 1‖) hfun).trans hsN
  have hcm := hc.mfderiv
  simp only [Function.comp_def] at hcm
  rw [hcm] at hnorm
  change ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp (n := n) x)
    ((0:ℝ) • v) ((1:ℝ) • v)‖=‖v‖ at hnorm
  simp only [one_smul] at hnorm
  exact (congrArg (fun w : V => ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n)
    (riemannianExp (n := n) x) w v‖) (zero_smul ℝ v)).symm.trans hnorm

lemma expJacobian_zero (x : M) : expJacobian (n := n) x 0=1 := by
  let F : TangentSpace 𝓘(ℝ,Model n) x →ₗ[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) := (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0).toLinearMap
  let e : TangentSpace 𝓘(ℝ,Model n) x →ₗᵢ[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x 0) :=
    { toLinearMap := F, norm_map' := mfderiv_exp_zero_norm x }
  exact e.normDet_eq_one

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma expJacobian_ne_zero_iff (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    expJacobian (n := n) x p≠0 ↔ Function.Injective
      (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) p) := by
  rw [expJacobian,ne_eq,LinearMap.normDet_eq_zero_iff_ker_ne_bot,not_not,
    LinearMap.ker_eq_bot]
  rfl

lemma expJacobian_pos_of_injectivityDomain {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) : 0<expJacobian (n := n) x p := by
  apply lt_of_le_of_ne (expJacobian_nonneg x p)
  apply Ne.symm
  rw [expJacobian_ne_zero_iff]
  have hcoord := mfderiv_comp p (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,Model n)) (mem_chart_source (Model n) (riemannianExp x p)))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv,mfderiv_extChartAt_self] at hcoord
  change fderiv ℝ _ p=mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
    𝓘(ℝ,Model n) (riemannianExp x) p at hcoord
  simp only [Function.comp_def] at hcoord
  erw [←hcoord]
  exact riemannianExp_interior_nonconjugate hp

end ExponentialJacobian
end WeakMTWTransport

end

end

end

end OAI
