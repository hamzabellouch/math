import Mathlib
import OAI.Analysis.BiholderTransport.Volume.ExponentialJacobian
import OAI.Analysis.BiholderTransport.LinearAlgebra.MatrixNormDetFactorial

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section IntrinsicJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteIntrinsicJacobian (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def chartJacobian (a x : M) : ℝ :=
  let F : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a) x
  F.toLinearMap.normDet

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartJacobian_nonneg (a x : M) : 0≤chartJacobian (n := n) a x :=
  LinearMap.normDet_nonneg _

lemma normDet_chart_exp (a x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (hp : riemannianExp (n := n) x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p).toLinearMap.normDet=
      chartJacobian (n := n) a (riemannianExp (n := n) x p)*expJacobian (n := n) x p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let E : V →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) :=
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) p
  let C : TangentSpace 𝓘(ℝ,Model n) (riemannianExp (n := n) x p) →L[ℝ] Model n :=
    mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) (extChartAt 𝓘(ℝ,Model n) a) (riemannianExp (n := n) x p)
  have hd := mfderiv_comp p (mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp))
    ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) p=C.comp E at hd
  rw [hd]
  exact LinearMap.normDet_comp_of_finrank_eq E.toLinearMap C.toLinearMap rfl

lemma normDet_chart_exp_zero (a x : M)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap.normDet=
      chartJacobian (n := n) a x := by
  have h := normDet_chart_exp a x 0 (by simpa only [riemannianExp_zero] using hx)
  rw [expJacobian_zero,mul_one] at h
  simpa only [riemannianExp_zero] using h

lemma intrinsic_contact_det {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (a b : M) (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hp : riemannianExp (n := n) x p∈(extChartAt 𝓘(ℝ,Model n) b).source)
    (W : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hR : (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
      ContinuousLinearMap.id ℝ (Model n)) :
    |((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p).comp (W.comp R)).det| *
      chartJacobian (n := n) a x=
      chartJacobian (n := n) b (riemannianExp (n := n) x p)*expJacobian (n := n) x p*|W.det| := by
  have hprod : chartJacobian (n := n) a x*R.toLinearMap.normDet=1 := by
    have h := congrArg (fun F : Model n →L[ℝ] Model n => F.toLinearMap.normDet) hR
    rw [show (ContinuousLinearMap.id ℝ (Model n)).toLinearMap=LinearMap.id by rfl,
      LinearMap.normDet_id] at h
    change ((fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap ∘ₗ
      R.toLinearMap).normDet=1 at h
    erw [LinearMap.normDet_comp_of_finrank_eq R.toLinearMap
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).toLinearMap rfl] at h
    rw [normDet_chart_exp_zero a x hx] at h
    exact h
  rw [←LinearMap.normDet_eq_abs_det]
  rw [normDet_comp_three R W _ rfl rfl,normDet_chart_exp b x p hp,
    LinearMap.normDet_eq_abs_det]
  calc
    _ = (chartJacobian (n := n) b (riemannianExp (n := n) x p)*expJacobian (n := n) x p*|W.det|)*
      (chartJacobian (n := n) a x*R.toLinearMap.normDet) := by ring
    _ = _ := by rw [hprod,mul_one]

end IntrinsicJacobian
end WeakMTWTransport

end

end

end

end OAI
