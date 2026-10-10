import Mathlib
import OAI.Geometry.SmoothYau.Model

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def bundleMetricInner (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  ((D x).precomp ℝ).comp ((g.inner x).comp (D x))

omit [FiniteDimensional ℝ E] in
lemma bundleMetricInner_apply (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    bundleMetricInner g D x v w = g.inner x (D x v) (D x w) := rfl

omit [FiniteDimensional ℝ E] in
lemma bundleMetricInner_smooth (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hD : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (D x))) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (bundleMetricInner g D x)) := by
  intro x₀
  have hd := hD x₀
  have hg := g.contMDiff x₀
  rw [contMDiffAt_section x₀] at hd hg ⊢
  have hh := hd.clm_precomp (F₃ := ℝ) |>.clm_comp (hg.clm_comp hd)
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  filter_upwards [hn] with x hx
  ext v w
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  rw [ContinuousLinearMap.inCoordinates_eq hx hx]
  simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp [bundleMetricInner_apply,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply,
    Trivialization.symm_apply_apply_mk _ hx]

def bundlePullbackMetric (g : SmoothMetric E M)
    (D : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hD : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (D x)))
    (hi : ∀ x, Function.Injective (D x)) : SmoothMetric E M where
  inner := bundleMetricInner g D
  symm x v w := g.symm x (D x v) (D x w)
  pos x v hv := g.pos x (D x v) (fun hz => hv (hi x (by simpa using hz)))
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : E | g.inner x (D x v) (D x v) < 1}
    have hd : Function.Injective (show E →L[ℝ] E from D x) := hi x
    obtain ⟨K,_,hK⟩ := (show E →L[ℝ] E from D x).toLinearMap.injective_iff_antilipschitz.mp hd
    rw [NormedSpace.isVonNBounded_iff ℝ]
    have hb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
      {v : E | g.inner x v v < 1} from g.isVonNBounded x)
    exact hK.isBounded_preimage hb
  contMDiff := bundleMetricInner_smooth g D hD

def bundleExp (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x :=
  show E →L[ℝ] E from NormedSpace.exp (show E →L[ℝ] E from K x)

lemma bundleExp_coordinates (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x₀ x : M) (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) E
      (TangentSpace 𝓘(ℝ,E)) x₀ x x₀ x (bundleExp K x) = NormedSpace.exp
      (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ,E)) E
        (TangentSpace 𝓘(ℝ,E)) x₀ x x₀ x (K x)) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  let e : E ≃L[ℝ] E := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).continuousLinearEquivAt ℝ x hx
  have hh := NormedSpace.map_exp e.conjContinuousAlgEquiv
    (e.arrowCongr e).continuous (show E →L[ℝ] E from K x)
  simp only [bundleExp]
  erw [ContinuousLinearMap.inCoordinates_eq hx hx, ContinuousLinearMap.inCoordinates_eq hx hx]
  convert hh using 1 <;> rfl

lemma bundleExp_smooth (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (bundleExp K x)) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiff
  intro x₀
  have hk := hK x₀
  rw [contMDiffAt_section x₀] at hk ⊢
  have hh := he.contMDiff.contMDiffAt.comp x₀ hk
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)] with x hx
  simp only [Function.comp_def,hom_trivializationAt_apply]
  exact bundleExp_coordinates K x₀ x hx

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma bundleExp_injective (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (x : M) : Function.Injective (bundleExp K x) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp (NormedSpace.isUnit_exp
    (show E →L[ℝ] E from K x))).1

def exponentialMetric (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) : SmoothMetric E M :=
  bundlePullbackMetric g (bundleExp K) (bundleExp_smooth K hK) (bundleExp_injective K)

end YauCounterexamples

end

end OAI
