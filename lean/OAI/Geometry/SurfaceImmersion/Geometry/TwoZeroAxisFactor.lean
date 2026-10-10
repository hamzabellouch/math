import OAI.Geometry.SurfaceImmersion.Correction.SmoothZeroFactor

namespace OAI

/-! Removing two simple zero factors from a vector-valued axis curve. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem nonzero_two_zero_factor {f : ℝ → V} (hf : ContDiff ℝ ∞ f)
    {p q : ℝ} (hpq : p ≠ q) (hp : f p = 0) (hq : f q = 0)
    (hdp : deriv f p ≠ 0) (hdq : deriv f q ≠ 0)
    {K : Set ℝ} (hz : ∀ t ∈ K, f t = 0 → t = p ∨ t = q) :
    ∃ d : ℝ → V, ContDiff ℝ ∞ d ∧ (∀ t, f t = ((t-p)*(t-q)) • d t) ∧
      (∀ t ∈ K, d t ≠ 0) ∧
      deriv f p = (p-q) • d p ∧ deriv f q = (q-p) • d q := by
  obtain ⟨d,hd,he,hep,heq⟩ := two_zero_smooth_factor hf hpq hp hq
  refine ⟨d,hd,he,?_,hep,heq⟩
  intro t ht hdt
  have hft : f t = 0 := by rw [he t,hdt,smul_zero]
  rcases hz t ht hft with rfl | rfl
  · exact hdp (by rw [hep,hdt,smul_zero])
  · exact hdq (by rw [heq,hdt,smul_zero])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
