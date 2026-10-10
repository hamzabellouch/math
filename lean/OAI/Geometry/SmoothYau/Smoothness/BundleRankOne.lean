import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def bundleRankOne (g : SmoothMetric E M) (V : ∀ x : M, TangentSpace 𝓘(ℝ,E) x) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  (g.inner x (V x)).smulRight (V x)

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_bundleRankOne (g : SmoothMetric E M)
    {V : ∀ x : M, TangentSpace 𝓘(ℝ,E) x} {p : M}
    (hv : ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun x => TotalSpace.mk' E x (V x)) p) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleRankOne g V x)) p := by
  rw [contMDiffAt_section p] at hv ⊢
  have hg := (contMDiffAt_localMetricFlat g p).clm_apply hv
  have hs : ContDiff ℝ ∞ (fun z : (E →L[ℝ] ℝ) × E => z.1.smulRight z.2) :=
    contDiff_fst.smulRight contDiff_snd
  have hprod := hg.prodMk hv
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hprod
  have hh := hs.contMDiff.contMDiffAt.comp p hprod
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  simp only [Function.comp_def,hom_trivializationAt_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hx hx]
  ext w
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    bundleRankOne,ContinuousLinearMap.smulRight_apply,map_smul,
    localMetricFlat_pairing g p x hx,
    Trivialization.symm_apply_apply_mk _ hx,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply]

omit [FiniteDimensional ℝ E] in
lemma contMDiff_bundleId :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ,E) x))) := by
  intro p
  rw [contMDiffAt_section p]
  apply (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ p)] with x hx
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.inCoordinates_eq hx hx]
  ext w
  simp

def bundleTransverse (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  ContinuousLinearMap.id ℝ _ -
    (g.inner x (metricGradient g u x) (metricGradient g u x))⁻¹ •
      bundleRankOne g (metricGradient g u) x

lemma contMDiffAt_bundleTransverse (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {p : M}
    (hp : metricGradient g u p ≠ 0) :
    ContMDiffAt 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleTransverse g u x)) p := by
  have hv := contMDiff_metricGradient g hu
  have hq := (g.contMDiff p).clm_bundle_apply₂ (hv p) (hv p)
  rw [contMDiffAt_totalSpace] at hq
  exact (contMDiff_bundleId p).sub_section
    ((hq.2.inv₀ (by simpa using (g.pos p _ hp).ne')).smul_section (contMDiffAt_bundleRankOne g (hv p)))

def supportedPinningTensor (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  let p := fun x => bundleTransverse g u x (metricGradient g v x)
  χ x • (bundleRankOne g p x - (g.inner x (p x) (p x) /2) • bundleTransverse g u x)

theorem supportedPinningTensor_smooth (g : SmoothMetric E M) {u v χ : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) {A : Set M}
    (hA : IsOpen A) (hs : tsupport χ ⊆ A) (hn : ∀ x ∈ A, metricGradient g u x ≠ 0) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (supportedPinningTensor g u v χ x)) := by
  apply ContMDiffOn.smul_section_of_tsupport (hχ.contMDiffOn) hA hs
  intro x hx
  have hP := contMDiffAt_bundleTransverse g hu (hn x hx)
  have hp := hP.clm_bundle_apply (contMDiff_metricGradient g hv x)
  have hq := (g.contMDiff x).clm_bundle_apply₂ hp hp
  rw [contMDiffAt_totalSpace] at hq
  exact ((contMDiffAt_bundleRankOne g hp).sub_section
    ((hq.2.div_const 2).smul_section hP)).contMDiffWithinAt
end YauCounterexamples

end

end OAI
