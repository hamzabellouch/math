import Mathlib
import OAI.Analysis.SymmetricDomains.IndependentComplexConormalRows
import OAI.Analysis.SymmetricDomains.SupportDifferentialsChangeChart
import OAI.Analysis.SymmetricDomains.RealDirectionsTangent

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

lemma forward_backward_boundary_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    (s.forward ∘ s.backward ∘ q) =ᶠ[𝓝 x] q := by
  simpa only [Function.comp_def,forward,backward,s.coordinates.symm_apply_apply,sub_add_cancel] using
    c.projection_inverse_germ hgood

lemma boundary_variety_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (hcut : s.HasCutoffs) (hq : ContinuousAt q x) :
    ∀ᶠ y in 𝓝 x, q y ∈ V := by
  have hback : ContinuousAt (s.backward ∘ q) x :=
    (s.backward_analytic (q x) (mem_univ _)).continuousAt.comp hq
  have hs : ∀ᶠ y in 𝓝 x, s.backward (q y) ∈ s.offsets.source := by
    apply hback.preimage_mem_nhds
    change s.offsets.source ∈ 𝓝 (s.backward (q x))
    rw [s.backward_center hgood]
    exact s.offsets.open_source.mem_nhds s.source_zero
  filter_upwards [hs,s.forward_backward_boundary_germ hgood] with y hy hyy
  rw [←show s.forward (s.backward (q y))=q y from hyy]
  exact s.forward_mem_variety hcut hy

theorem independent_support_rows (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0=q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V)
    {k : ℕ} (h : Fin k → Affine N → ℂ)
    (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0)
    (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap))
    (hzero : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ q) x)=0) :
    (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (s.forward z))) 0) ∧
    ∃ β : Fin k → Fin s.normalDim → ℝ, LinearIndependent ℝ β ∧
      ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
        Complex.I * ∑ j, (β i j : ℂ)*z.2 j := by
  have hG0 : G (q x)=0 := by simpa only [Function.comp_apply,hF0,id_eq] using hGF.eq_of_nhds
  have hsf := s.forward_analytic hcut 0 s.source_zero
  have hsg := s.backward_analytic (q x) (mem_univ _)
  have hbgf : (s.backward ∘ s.forward) =ᶠ[𝓝 (0 : Affine s.tangentDim × Affine s.normalDim)] id := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hsfV : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim), s.forward z ∈ V := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.forward_mem_variety hcut hz
  obtain ⟨A,hA,hchart⟩ := analytic_chart_transition s.forward s.backward F G
    (s.forward_zero hgood) hF0 hsf hsg hF hG hbgf hGF
    (s.forward_backward_germ hgood F G hF0 hF hG hGF hFG) hFG hsfV hFV
  have hT0 : (G ∘ s.forward) 0=0 := by simp only [Function.comp_apply,s.forward_zero hgood,hG0]
  have hT : AnalyticAt ℂ (G ∘ s.forward) 0 := ((s.forward_zero hgood).symm ▸ hG).comp hsf
  obtain ⟨hnew,hnewI⟩ := support_differentials_change_chart h s.forward F (G ∘ s.forward)
    hT0 hT hchart hlog hI A hA
  have hqV := s.boundary_variety_germ hgood hcut hq.continuousAt
  have htq : Tendsto q (𝓝 x) (𝓝[V] (q x)) := tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hzeroNew (i : Fin k) : (fderiv ℝ (fun z => Real.log ‖h i (s.forward z)‖) 0).comp
      (fderiv ℝ (s.backward ∘ q) x)=0 := by
    have hdold := support_along_chart_fderiv (h i) F G q hG0 (hG.differentiableAt.restrictScalars ℝ)
      hq (htq hFG) (hlog i)
    have hdnew := support_along_chart_fderiv (h i) s.forward s.backward q
      (s.backward_center hgood) (hsg.differentiableAt.restrictScalars ℝ) hq
      (s.forward_backward_boundary_germ hgood) (hnew i)
    exact hdnew.symm.trans (hdold.trans (hzero i))
  let L : Fin k → (Affine s.tangentDim × Affine s.normalDim) →ₗ[ℂ] ℂ :=
    fun i => (fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0).toLinearMap
  have he : (fun i => (fderiv ℝ (fun z => Real.log ‖h i (s.forward z)‖) 0).toLinearMap) =
      (fun i => Complex.reLm.comp ((L i).restrictScalars ℝ)) := by
    funext i
    rw [log_norm_fderiv _ (hnew i)]
    rfl
  have hLI : LinearIndependent ℝ (fun i => Complex.reLm.comp ((L i).restrictScalars ℝ)) := he ▸ hnewI
  have hLzero : ∀ i (z : Affine s.tangentDim) (w : Fin s.normalDim → ℝ), (L i (z,fun j => (w j : ℂ))).re=0 := by
    intro i z w
    obtain ⟨v,hv⟩ := s.real_directions_tangent hgood hq hqi hr z w
    have hh := congrArg (fun M : (Fin d → ℝ) →L[ℝ] ℝ => M v) (hzeroNew i)
    rw [ContinuousLinearMap.comp_apply,hv,log_norm_fderiv _ (hnew i)] at hh
    exact hh
  obtain ⟨β,hβ,hβeq⟩ := independent_complex_conormal_rows L hLzero hLI
  exact ⟨hnew,β,hβ,fun i z => hβeq i z.1 z.2⟩
end NashBoundaryScalingChart
end Release061

end

end OAI
