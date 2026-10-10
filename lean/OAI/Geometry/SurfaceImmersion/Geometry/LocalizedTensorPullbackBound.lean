import OAI.Geometry.SurfaceImmersion.Atlas.TensorCoordinatePullbackBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedCompositionBounds

namespace OAI

/-! The supported tensor pullback has a fixed weighted norm on each finite order. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def localizedTensorPullback (T : Base → Base) (χ : Base → ℝ)
    (f : Base → PhaseMean.Tensor) (x : Base) : PhaseMean.Tensor :=
  χ x • tensorCoordinatePullbackValue T x (f (T x))

lemma localizedTensorPullback_smooth {T : Base → Base} {χ : Base → ℝ}
    {f : Base → PhaseMean.Tensor} (hT : ContDiff ℝ ∞ T) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (localizedTensorPullback T χ f) :=
  hχ.smul ((tensorCoordinatePullbackValue_smooth hT).clm_apply (hf.comp hT))

theorem localized_tensor_pullback_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {O W : Set Base} (hO : IsOpen O) (hW : IsOpen W)
    (hχO : tsupport χ ⊆ O) (hTW : MapsTo T O W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound W s m C f →
      WeightedBound univ s m (D*C) (localizedTensorPullback T χ f) := by
  obtain ⟨V,hV,hχV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure hc hO hχO
  have hsub : V ⊆ O := subset_closure.trans hVO
  obtain ⟨D,hD,hd⟩ := fixed_tensor_coordinate_bound hT hV hVc hW (hTW.mono_left hsub) m
  obtain ⟨A,hA,ha⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) hχ.contDiffOn m
  refine ⟨2^m*A*D,by positivity,?_⟩
  intro f s C hs hs1 hC hf hb
  have hp := (ha s hs.le hs1).smul_real hV.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (mul_nonneg hD hC) hχ.contDiffOn
    (((tensorCoordinatePullbackValue_smooth hT).clm_apply (hf.comp hT)).contDiffOn)
    (hd f s C hs hs1 hC hf.contDiffOn hb)
  have hg := localizedTensorPullback_smooth hT hχ hf
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ V
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (localizedTensorPullback T χ f) x :=
      (hg.of_le (by simp)).contDiffAt
    have hh := hp j hj x hx
    change s^j * ‖iteratedFDerivWithin ℝ j (localizedTensorPullback T χ f) V x‖ ≤ _ at hh
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn ht hx] at hh
    convert hh using 1
    first | rfl | ring
  · have hz : x ∉ tsupport χ := fun hx' => hx (hχV hx')
    have heq : localizedTensorPullback T χ f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [localizedTensorPullback,hy,zero_smul]
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero,mul_zero]
    positivity

end ClosedSurfaceR4.JetPolynomial

end

end OAI
