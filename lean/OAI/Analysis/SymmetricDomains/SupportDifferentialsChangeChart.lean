import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicSupportIndependent

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
open Set Filter Topology
open scoped Classical

theorem analytic_chart_transition
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {V : Set H} {p : H} (f : E → H) (g : H → E) (Φ : F → H) (Ψ : H → F)
    (hf0 : f 0=p) (hΦ0 : Φ 0=p)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g p)
    (hΦ : AnalyticAt ℂ Φ 0) (hΨ : AnalyticAt ℂ Ψ p)
    (hgf : (g ∘ f) =ᶠ[𝓝 (0 : E)] id) (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 (0 : F)] id)
    (hfg : ∀ᶠ y in 𝓝[V] p, f (g y)=y) (hΦΨ : ∀ᶠ y in 𝓝[V] p, Φ (Ψ y)=y)
    (hfV : ∀ᶠ z in 𝓝 (0 : E), f z ∈ V) (hΦV : ∀ᶠ z in 𝓝 (0 : F), Φ z ∈ V) :
    ∃ A : E ≃L[ℂ] F, A.toContinuousLinearMap = fderiv ℂ (Ψ ∘ f) 0 ∧
      (Φ ∘ (Ψ ∘ f)) =ᶠ[𝓝 (0 : E)] f := by
  have hg0 : g p=0 := by simpa only [Function.comp_apply,hf0,id_eq] using hgf.eq_of_nhds
  have hΨ0 : Ψ p=0 := by simpa only [Function.comp_apply,hΦ0,id_eq] using hΨΦ.eq_of_nhds
  let T := Ψ ∘ f
  let S := g ∘ Φ
  have hT0 : T 0=0 := by simp only [T,Function.comp_apply,hf0,hΨ0]
  have hS0 : S 0=0 := by simp only [S,Function.comp_apply,hΦ0,hg0]
  have hT : AnalyticAt ℂ T 0 := (hf0.symm ▸ hΨ).comp hf
  have hS : AnalyticAt ℂ S 0 := (hΦ0.symm ▸ hg).comp hΦ
  have ht : Tendsto f (𝓝 (0 : E)) (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hf0 ▸ hf.continuousAt,hfV⟩
  have hs : Tendsto Φ (𝓝 (0 : F)) (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hΦ0 ▸ hΦ.continuousAt,hΦV⟩
  have hΦT : (Φ ∘ T) =ᶠ[𝓝 (0 : E)] f := ht hΦΨ
  have hST : (S ∘ T) =ᶠ[𝓝 (0 : E)] id := by
    filter_upwards [hΦT,hgf] with z hz hzz
    change g (Φ (T z))=z
    rw [show Φ (T z)=f z from hz]
    exact hzz
  have hTS : (T ∘ S) =ᶠ[𝓝 (0 : F)] id := by
    filter_upwards [hs hfg,hΨΦ] with z hz hzz
    change Ψ (f (g (Φ z)))=z
    rw [hz]
    exact hzz
  let A := fderiv ℂ T 0
  let B := fderiv ℂ S 0
  have hBA : B.comp A = ContinuousLinearMap.id ℂ E := by
    have hSa : AnalyticAt ℂ S (T 0) := hT0.symm ▸ hS
    have hd := ((hSa.differentiableAt.hasFDerivAt.comp 0 hT.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hST.symm).unique (hasFDerivAt_id 0)
    simpa only [hT0] using hd
  have hAB : A.comp B = ContinuousLinearMap.id ℂ F := by
    have hTa : AnalyticAt ℂ T (S 0) := hS0.symm ▸ hT
    have hd := ((hTa.differentiableAt.hasFDerivAt.comp 0 hS.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hTS.symm).unique (hasFDerivAt_id 0)
    simpa only [hS0] using hd
  refine ⟨ContinuousLinearEquiv.equivOfInverse A B ?_ ?_,rfl,hΦT⟩
  · intro z
    change (B.comp A) z=z
    rw [hBA,ContinuousLinearMap.id_apply]
  · intro z
    change (A.comp B) z=z
    rw [hAB,ContinuousLinearMap.id_apply]

theorem support_differentials_change_chart
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {ι : Type*} (h : ι → H → ℂ) (f : E → H) (Φ : F → H) (T : E → F)
    (hT0 : T 0=0) (hT : AnalyticAt ℂ T 0)
    (hchart : (Φ ∘ T) =ᶠ[𝓝 (0 : E)] f)
    (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) 0)
    (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (Φ z)‖) 0).toLinearMap))
    (A : E ≃L[ℂ] F) (hA : A.toContinuousLinearMap = fderiv ℂ T 0) :
    (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (f z))) 0) ∧
    LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (f z)‖) 0).toLinearMap) := by
  have he (i : ι) : (fun z => Complex.log (h i (Φ (T z)))) =ᶠ[𝓝 (0 : E)]
      (fun z => Complex.log (h i (f z))) := hchart.mono (fun z hz => congrArg (fun y => Complex.log (h i y)) hz)
  have ha (i : ι) : AnalyticAt ℂ (fun z => Complex.log (h i (Φ (T z)))) 0 :=
    (hT0.symm ▸ hlog i).comp hT
  have ha' (i : ι) := (ha i).congr (he i)
  refine ⟨ha',?_⟩
  have hd (i : ι) : fderiv ℝ (fun z => Real.log ‖h i (f z)‖) 0 =
      (fderiv ℝ (fun z => Real.log ‖h i (Φ z)‖) 0).comp (A.toContinuousLinearMap.restrictScalars ℝ) := by
    rw [log_norm_fderiv _ (ha' i),log_norm_fderiv _ (hlog i)]
    have hℂ : fderiv ℂ (fun z => Complex.log (h i (f z))) 0 =
        (fderiv ℂ (fun z => Complex.log (h i (Φ z))) 0).comp A.toContinuousLinearMap := by
      have hlogT : AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) (T 0) := hT0.symm ▸ hlog i
      have hh := (hlogT.differentiableAt.hasFDerivAt.comp 0 hT.differentiableAt.hasFDerivAt).congr_of_eventuallyEq (he i).symm
      simpa only [hT0,←hA] using hh.fderiv
    rw [hℂ]
    rfl
  let R : E ≃ₗ[ℝ] F := A.toLinearEquiv.restrictScalars ℝ
  have hi : Function.Injective R.toLinearMap.dualMap :=
    LinearMap.dualMap_injective_of_surjective R.surjective
  have hmap := hI.map' R.toLinearMap.dualMap (LinearMap.ker_eq_bot.mpr hi)
  simp_rw [hd]
  exact hmap
end Release061

end

end OAI
