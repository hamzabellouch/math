import Mathlib
import OAI.Analysis.BiholderTransport.Volume.UniformJacobian
import OAI.Analysis.BiholderTransport.CostGeometry.UniformReverseGain

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma regular_divided_hessian_decrease {y:M} {p d:TangentSpace 𝓘(ℝ,Model n) y}
    (hp:p∈injectivityDomain y) {s:ℝ} (hs:0<s) (hs1:s<1) :
    hessianValue y p d ≤ hessianValue y (s • p) d/s := by
  by_cases hd:d=0
  · subst d
    rw [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian
      (contracted_minimizer_mem_injectivityDomain
        (injectivityDomain_subset_minimizingVectors y hp) hs hs1)]
    simp
  · exact (hessianValue_strict_radial_decrease hp hs hs1 hd).le

lemma exists_uniform_true_center_gain :
    ∃c>0,∀ᶠ l:ℝ in 𝓝 1,l<1 → ∀x:M,∀q:TangentSpace 𝓘(ℝ,Model n) x,
    ∀p:TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      p∈injectivityDomain (riemannianExp x q) → q∈injectivityDomain x →
      riemannianExp (riemannianExp x q) (l • p)=x →
      ∀R:TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x q),
      DifferentiableAt ℝ R q → R q=0 →
      (∀ᶠ z in 𝓝 q,riemannianExp (riemannianExp x q) (R z)=riemannianExp x z) →
      ∀d,c*(1-l)*‖d‖^2 ≤
        normalHessian (riemannianExp x q) (l • p) (fderiv ℝ R q d) (fderiv ℝ R q d)-
        l*normalHessian (riemannianExp x q) p (fderiv ℝ R q d) (fderiv ℝ R q d) := by
  obtain ⟨c,hc,H⟩:=exists_uniform_reverse_divided_gain (n:=n) (M:=M)
  have hpair:Tendsto (fun l:ℝ=>(l,(1+l)/2)) (𝓝 1) (𝓝 (1,1)):=by
    have hh:ContinuousAt (fun l:ℝ=>(l,(1+l)/2)) (1:ℝ):=
      continuousAt_id.prodMk ((continuousAt_const.add continuousAt_id).div_const 2)
    simpa using hh.tendsto
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hpair.eventually H,eventually_gt_nhds (by norm_num : (1/2:ℝ)<1)] with l hl hhalf
  intro hl1 x q p hp hq hpx R hR hR0 hRe d
  have hl0:0<l:=by linarith
  have hs0:0<(1+l)/2:=by positivity
  have hs1:(1+l)/2<1:=by linarith
  have hls:l≤(1+l)/2:=by linarith
  have hpm:=injectivityDomain_subset_minimizingVectors _ hp
  obtain ⟨S,hS,hS0,hSe,HS⟩:=hl hls hs1 (riemannianExp x q) x p q hpm hq hpx rfl
  have hder:fderiv ℝ S q=fderiv ℝ R q:=by
    ext w
    rw [normal_endpoint_derivative_eq (hS.differentiableAt (by simp)) hS0 hSe,
      normal_endpoint_derivative_eq hR hR0 hRe]
  rw [hder] at HS
  have HA:=regular_divided_hessian_decrease hp hs0 hs1 (d:=fderiv ℝ R q d)
  have HD:=mul_le_mul_of_nonneg_left (HS d) hl0.le
  have HE:l*(hessianValue (riemannianExp x q) (l • p) (fderiv ℝ R q d)/l-
      hessianValue (riemannianExp x q) (((1+l)/2) • p) (fderiv ℝ R q d)/((1+l)/2))=
      hessianValue (riemannianExp x q) (l • p) (fderiv ℝ R q d)-
      l*(hessianValue (riemannianExp x q) (((1+l)/2) • p) (fderiv ℝ R q d)/((1+l)/2)):=by
    field_simp
  rw [HE] at HD
  have HG:(c/4)*(1-l)*‖d‖^2 ≤ l*(c*((1+l)/2-l)*‖d‖^2):=by
    nlinarith only [mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖d‖),
      mul_nonneg (sub_nonneg.mpr hhalf.le)
        (mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hl1.le)) (sq_nonneg ‖d‖))]
  have HT:=mul_le_mul_of_nonneg_left HA hl0.le
  rw [hessianValue_eq_normalHessian hp] at HT
  rw [hessianValue_eq_normalHessian
    (contracted_minimizer_mem_injectivityDomain hpm hl0 hl1)] at HD
  linarith only [HD,HG,HT]
end WeakMTWTransport

end

end OAI
