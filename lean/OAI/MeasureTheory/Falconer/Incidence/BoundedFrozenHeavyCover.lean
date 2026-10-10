import OAI.MeasureTheory.Falconer.Incidence.FrozenHeavyCover
import OAI.MeasureTheory.Falconer.Geometry.TubeAnchorNet

namespace OAI

/-! # Heavy radial fibers have bounded-anchor frozen tube covers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem bounded_frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ J : Finset (Space (n+1)),
      (∀ a ∈ J, ‖a‖ ≤ B) ∧
      (∀ z ∈ T, ∃ a ∈ J, ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤
        (2*((n+1:ℕ):ℝ)+1)*δ) ∧
      (J.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ x c hr hcx hδ hfreeze hsource T hT F hheavy L hL
  obtain ⟨K,hKb,hKn⟩ := exists_bounded_anchor_net (d := n+1) B hδ
  let w : Sphere (n+1) := ⟨normalize (c-x),by
    rw [Metric.mem_sphere,dist_zero_right]
    exact norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))⟩
  obtain ⟨J,hJK,hJP,hJ⟩ := rounded_tube_cover w T P K
    (fun z hz => hKn z (hT z hz).2.2) hP
  refine ⟨J,fun a ha => hKb a (hJK ha),?_,?_⟩
  · intro z hz
    obtain ⟨a,ha,hza⟩ := hJ z hz
    refine ⟨a,ha,?_⟩
    change ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤ _ at hza
    convert hza using 1
    ring
  · have hc : (J.card:ℝ≥0∞) ≤ P.card := by exact_mod_cast hJP
    exact (mul_le_mul' hc le_rfl).trans hcard

end Falconer

end OAI
