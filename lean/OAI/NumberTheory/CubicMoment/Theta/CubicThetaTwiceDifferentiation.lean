import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace OAI

/-! Local twice differentiation for the complex coordinate series used
below. Both summable derivative bounds are supplied by actual grid estimates. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_twice_hasDerivAt_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hf : ∀ i t, t ∈ Set.Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (f i) t‖ ≤ u₁ i)
    (h₂ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (deriv (f i)) t‖ ≤ u₂ i)
    (h₀ : Summable (fun i => f i x)) :
    HasDerivAt (fun t => ∑' i, f i t) (∑' i, deriv (f i) x) x ∧
    HasDerivAt (deriv (fun t => ∑' i, f i t)) (∑' i, deriv (deriv (f i)) x) x ∧
    Summable (fun i => deriv (f i) x) ∧
    Summable (fun i => deriv (deriv (f i)) x) := by
  have hd₁ t (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun w => ∑' i, f i w) (∑' i, deriv (f i) t) t :=
    hasDerivAt_tsum_of_isPreconnected hu₁ isOpen_Ioo (convex_Ioo a b).isPreconnected
      (fun i w hw => (hf i w hw).differentiableAt.hasDerivAt) h₁ hx h₀ ht
  have hs₁ : Summable (fun i => deriv (f i) x) :=
    hu₁.of_norm_bounded (fun i => h₁ i x hx)
  have hs₂ : Summable (fun i => deriv (deriv (f i)) x) :=
    hu₂.of_norm_bounded (fun i => h₂ i x hx)
  have hd₂ : HasDerivAt (fun t => ∑' i, deriv (f i) t)
      (∑' i, deriv (deriv (f i)) x) x :=
    hasDerivAt_tsum_of_isPreconnected hu₂ isOpen_Ioo (convex_Ioo a b).isPreconnected
      (fun i w hw => (hf i w hw).deriv.differentiableAt.hasDerivAt) h₂ hx hs₁ hx
  have he : deriv (fun t => ∑' i, f i t) =ᶠ[𝓝 x] (fun t => ∑' i, deriv (f i) t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact (hd₁ t ht).deriv
  exact ⟨hd₁ x hx,hd₂.congr_of_eventuallyEq he,hs₁,hs₂⟩

lemma cubicTheta_twice_deriv_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hf : ∀ i t, t ∈ Set.Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (f i) t‖ ≤ u₁ i)
    (h₂ : ∀ i t, t ∈ Set.Ioo a b → ‖deriv (deriv (f i)) t‖ ≤ u₂ i)
    (h₀ : Summable (fun i => f i x)) :
    deriv (fun t => ∑' i, f i t) x=(∑' i, deriv (f i) x) ∧
    deriv (deriv (fun t => ∑' i, f i t)) x=(∑' i, deriv (deriv (f i)) x) ∧
    Summable (fun i => deriv (f i) x) ∧
    Summable (fun i => deriv (deriv (f i)) x) := by
  obtain ⟨h,h',hs,hs'⟩ := cubicTheta_twice_hasDerivAt_tsum hu₁ hu₂ hx hf h₁ h₂ h₀
  exact ⟨h.deriv,h'.deriv,hs,hs'⟩

end CubicFirstMoment

end

end OAI
