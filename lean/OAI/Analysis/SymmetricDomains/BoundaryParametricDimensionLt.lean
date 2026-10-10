import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash

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

theorem boundary_parametric_dimension_lt {d m N : ℕ}
    {U V : Set (Affine N)} (hUV : U ⊆ V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hp : q x ∈ closure U) (hF0 : F 0 = q x)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : AnalyticAt ℝ q x) (hqinj : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFGV : ∀ᶠ y in 𝓝[V] (q x), F (G y) = y)
    (hqV : ∀ᶠ y in 𝓝 x, q y ∈ V)
    (hqnU : ∀ᶠ y in 𝓝 x, q y ∉ U) : d < 2*m := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have ht : Tendsto q (𝓝 x) (𝓝[V] (q x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hFGq : (F ∘ G ∘ q) =ᶠ[𝓝 x] q := ht hFGV
  let r := G ∘ q
  have hr : AnalyticAt ℝ r x := hG.restrictScalars.comp hq
  have hd : ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ r x) = fderiv ℝ q x := by
    have hf' : AnalyticAt ℂ F (r x) := by simpa only [r,Function.comp_apply,hG0] using hF
    have hh := (hf'.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.differentiableAt.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFGq.symm
    simpa only [r,Function.comp_apply,hG0] using he.fderiv.symm
  have hi : Function.Injective (fderiv ℝ r x) := by
    intro a b hab
    apply hqinj
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  have hdim : Module.finrank ℝ (Affine m) = 2*m := by simp [Affine,Module.finrank_pi_fintype,Nat.mul_comm]
  have hle : d ≤ 2*m := by
    have hh := (fderiv ℝ r x).toLinearMap.finrank_le_finrank_of_injective hi
    simpa only [Module.finrank_pi,Fintype.card_fin,hdim] using hh
  apply lt_of_le_of_ne hle
  intro heq
  have hedim : Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (Affine m) := by
    simpa using heq.trans hdim.symm
  let e := ((fderiv ℝ r x).toLinearMap.linearEquivOfInjective hi hedim).toContinuousLinearEquiv
  have he : (e : (Fin d → ℝ) →L[ℝ] Affine m) = fderiv ℝ r x := by ext v; rfl
  have hs : HasStrictFDerivAt r (e : (Fin d → ℝ) →L[ℝ] Affine m) x := by
    rw [he]; exact hr.hasStrictFDerivAt
  let B : Set (Fin d → ℝ) := {y | F (G (q y)) = q y ∧ q y ∉ U}
  have hB : B ∈ 𝓝 x := hFGq.and hqnU
  have hBr : r '' B ∈ 𝓝 (r x) := by
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map hB
  have hGBr : ∀ᶠ y in 𝓝 (q x), G y ∈ r '' B := hG.continuousAt hBr
  have hFGU : ∀ᶠ y in 𝓝[U] (q x), F (G y) = y :=
    hFGV.filter_mono (nhdsWithin_mono _ hUV)
  have hfalse : ∀ᶠ y in 𝓝[U] (q x), False := by
    filter_upwards [self_mem_nhdsWithin,hFGU,
      mem_nhdsWithin_of_mem_nhds hGBr] with y hy he hyB
    obtain ⟨t,htB,ht⟩ := hyB
    have hty : q t = y := by
      rw [← htB.1]
      change F (r t) = y
      rw [ht,he]
    exact htB.2 (hty.symm ▸ hy)
  have : NeBot (𝓝[U] (q x)) := mem_closure_iff_nhdsWithin_neBot.mp hp
  exact hfalse.exists.elim (fun _ h => h)
end Release061

end

end OAI
