import OAI.MeasureTheory.Falconer.Angular.TubeDirectionRobustness

namespace OAI

/-! # One good witness direction rules out mass in a nearby heavy tube cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem mass_lt_of_good_direction_cover (μ : Measure (Space d))
    (Bad : Set (Sphere d)) (v : Sphere d) (hv : v ∉ Bad)
    (w : Space d) (hw : ‖w‖ = 1) {D B η r R : ℝ}
    (hdir : ‖w-(v:Space d)‖ ≤ η ∨ ‖w+(v:Space d)‖ ≤ η)
    (hwidth : r+2*η*(D+B) ≤ R) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (J : Finset (Space d)) (hJ : ∀ a ∈ J, ‖a‖ ≤ B) (N : ℕ) (hcard : J.card ≤ N)
    (a : ℝ≥0∞)
    (henvelope : ∀ S : Finset (Space d), S.card ≤ N →
      a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (v:Space d) (x-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space d))
    (hcover : ∀ x ∈ T, ∃ b ∈ J, ‖perpendicularPart w (x-b)‖ ≤ r) : μ T < a := by
  by_contra hn
  have hlarge : a ≤ μ T := le_of_not_gt hn
  apply hv
  apply henvelope J hcard
  apply hlarge.trans
  apply (measure_mono hcover).trans
  apply (tube_cover_direction_transport μ hw (sphere_norm v) hdir hμ J hJ).trans
  apply measure_mono
  rintro x ⟨b,hb,hxb⟩
  exact ⟨b,hb,hxb.trans hwidth⟩

end Falconer

end OAI
