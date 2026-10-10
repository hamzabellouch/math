import OAI.NumberTheory.JointDickman.Analysis.CharacterContourBounds

namespace OAI

/-! # A single uniform majorant for all three shifted contour edges -/
namespace JointDickman
open Complex Set

theorem characterContourSeries_closed_rectangle_bound {z η : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ δ c T : ℝ, 0 < δ → δ ≤ η → c ≤ 1/2 → 0 < T →
      ∀ f : ℂ → ℂ,
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = χ.LFunction s) →
      ∀ w : ℂ, -δ/2 ≤ w.re → w.re ≤ c → |w.im| ≤ T →
      ‖characterContourSeries χ z f (1+w)‖ ≤ C*(((q:ℝ)+2)*(T+2))^η := by
  obtain ⟨C,hC,hb⟩ := characterContourSeries_rectangle_bound hz hz1 hη hη1
  refine ⟨C,hC,?_⟩
  intro q _ χ hn δ c T hδ hδη hc hT f he w hw hwc hwi
  have hmem : 1+w ∈ zetaOpenRectangle δ (2*T) := by
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧
      (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re, one_re, add_im, one_im, zero_add]
    obtain ⟨hwmin,hwmax⟩ := abs_le.mp hwi
    constructor <;> constructor <;> linarith
  apply hb q χ hn f T hT.le (1+w) _ _ _ (he (1+w) hmem)
  · simp only [add_re, one_re]
    linarith
  · simp only [add_re, one_re]
    linarith
  · simpa only [add_im, one_im, zero_add] using hwi

end JointDickman

end OAI
