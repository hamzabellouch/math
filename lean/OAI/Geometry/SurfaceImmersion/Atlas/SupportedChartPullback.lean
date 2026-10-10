import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedCompositionBounds
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Compactly supported pullback through a local chart, extended by a fixed
cutoff without altering the pullback on the chart's source. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def supportedChartPullback (e : OpenPartialHomeomorph Base Base) (χ : Base → ℝ)
    (f : Base → V) (x : Base) : V := χ x • f (e x)

lemma supportedChartPullback_smooth (e : OpenPartialHomeomorph Base Base)
    {χ : Base → ℝ} {f : Base → V} (he : ContDiff ℝ ∞ e)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (supportedChartPullback e χ f) := hχ.smul (hf.comp he)

lemma supportedChartPullback_support (e : OpenPartialHomeomorph Base Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ} {f : Base → V} {K : Set Base}
    (hK : IsCompact K) (hχ : tsupport χ ⊆ e.source) (hf : tsupport f ⊆ K) :
    tsupport (supportedChartPullback e χ f) ⊆ e.symm '' K := by
  apply closure_minimal _ (hK.image hi.continuous).isClosed
  intro x hx
  have hn : χ x • f (e x) ≠ 0 := hx
  have hc : χ x ≠ 0 := fun hz => hn (by rw [hz,zero_smul])
  have hfx : f (e x) ≠ 0 := fun hz => hn (by rw [hz,smul_zero])
  exact ⟨e x,hf (subset_tsupport f hfx),e.left_inv (hχ (subset_tsupport χ hc))⟩

lemma supportedChartPullback_eq (e : OpenPartialHomeomorph Base Base)
    {χ : Base → ℝ} {f : Base → V} {K : Set Base}
    (hf : tsupport f ⊆ K) (hχ : ∀ x ∈ e.symm '' K, χ x = 1)
    {x : Base} (hx : x ∈ e.source) :
    supportedChartPullback e χ f x = f (e x) := by
  by_cases hz : f (e x) = 0
  · simp only [supportedChartPullback,hz,smul_zero]
  · have hxK : x ∈ e.symm '' K := ⟨e x,hf (subset_tsupport f hz),e.left_inv hx⟩
    simp only [supportedChartPullback,hχ x hxK,one_smul]

lemma supportedChartPullback_bound (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport χ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C) (supportedChartPullback e χ f) :=
  compact_localized_composition_bound isOpen_univ hcompact (subset_univ _)
    hχ (Subset.rfl) he.contDiffOn m

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
