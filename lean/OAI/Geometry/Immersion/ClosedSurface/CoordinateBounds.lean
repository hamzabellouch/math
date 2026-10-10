import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import OAI.Geometry.Immersion.ClosedSurface.OscillatoryModel
import OAI.Geometry.Immersion.ClosedSurface.NormalFrame
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]




lemma WeightedBound.comp_coordinates {U : Set E} {V : Set F}
    (hU : UniqueDiffOn ℝ U) (hV : UniqueDiffOn ℝ V) {s C D : ℝ} {m : ℕ}
    {f : E → F} {g : F → G} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hUV : MapsTo f U V)
    (hcoord : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U, ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C)
    (hb : WeightedBound V s m D g) :
    WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (g ∘ f) := by
  intro j hj x hx
  have hi (i : ℕ) (hi1 : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ C ^ i := by
    refine (hcoord i hi1 (hij.trans hj) x hx).trans ?_
    simpa only [pow_one] using pow_le_pow_right₀ hC hi1
  have ho (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i g V (f x)‖ ≤ D / s ^ j := by
    refine (hb.deriv_le hs (hij.trans hj) (hUV hx)).trans ?_
    exact div_le_div_of_nonneg_left hD (pow_pos hs _) (pow_le_pow_of_le_one hs.le hs1 hij)
  have hn : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have hh := norm_iteratedFDerivWithin_comp_le hg hf hn hV hU hUV hx ho hi
  calc
    _ ≤ s ^ j * ((j.factorial : ℝ) * (D / s ^ j) * C ^ j) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = (j.factorial : ℝ) * D * C ^ j := by field_simp
    _ ≤ (m.factorial : ℝ) * D * C ^ m := by gcongr

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
