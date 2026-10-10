import OAI.MeasureTheory.Falconer.Radial.HeavyPlateCover
import OAI.MeasureTheory.Falconer.Radial.FinitePlateException

namespace OAI

/-! # Newly deleted pairs outside the exceptional first endpoints have small fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem late_plate_fiber_bound (ν ρ : Measure (Space d)) (Q : DyadicCube d)
    (j j' : ℕ) (S : Finset (Space d × ℝ)) (G : Set (Space d × Space d))
    {r m r' m' R τ M : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (hwidth : 2*M*τ+3*R ≤ r') (hν : ν ≤ ρ)
    (hbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hG : G ⊆ heavyPlateCellPairs ρ Q j r m \ heavyPlateCellPairs ρ Q j' r' m')
    (hcover : heavyPlateCellPairs ρ Q j r m ⊆
      ⋃ p ∈ S, {x | |inner ℝ p.1 x-p.2| ≤ R} ×ˢ {y | |inner ℝ p.1 y-p.2| ≤ R})
    (x : Space d) (hx : ‖x‖ ≤ M) (hgood : x ∉ slabPairException S R τ) :
    ν {y | (x,y) ∈ G} ≤ ENNReal.ofReal m' := by
  classical
  let F := {y | (x,y) ∈ G}
  by_cases hF : F.Nonempty
  · obtain ⟨y₀,hy₀⟩ := hF
    obtain ⟨p,hp,hxp,hyp⟩ := mem_iUnion₂.mp (hcover (hG hy₀).1)
    have hRr : R ≤ r' := by
      have hMT := mul_nonneg hM hτ
      nlinarith only [hwidth,hMT,hR]
    have hxfar : |inner ℝ p.1 x-p.2| ≤ r' := hxp.trans hRr
    have hfiber : ∀ᵐ y ∂ν, y ∈ F → |inner ℝ p.1 y-p.2| ≤ r' := by
      filter_upwards [hbounded] with y hy hGy
      obtain ⟨q,hq,hxq,hyq⟩ := mem_iUnion₂.mp (hcover (hG hGy).1)
      exact (cluster_outside_slabPairException S hx hgood hp hxp q hq hxq y hy hyq).trans hwidth
    by_cases hmass : ρ {y | |inner ℝ p.1 y-p.2| ≤ r'} ≤ ENNReal.ofReal m'
    · exact (measure_mono_ae hfiber).trans ((hν _).trans hmass)
    · have hempty : ν F ≤ ν (∅ : Set (Space d)) := by
        apply measure_mono_ae
        filter_upwards [hfiber] with y hy hGy
        have hroot := heavyPlateCellPairs_subset_root ρ Q j r m (hG hGy).1
        exact (hG hGy).2 (heavyPlateCellPairs_of_points ρ Q j' r' m'
          hroot.1 hroot.2 (hunit p hp) (not_le.mp hmass).le hxfar (hy hGy))
      exact hempty.trans (by simp only [measure_empty]; exact bot_le)
  · have he : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    change ν F ≤ _
    rw [he,measure_empty]
    exact bot_le

end Falconer

end OAI
