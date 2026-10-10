import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry
import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem exists_bounded_anchor_net (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ a ∈ S, ‖a‖ ≤ D) ∧
      ∀ x : Space d, ‖x‖ ≤ D → ∃ a ∈ S, ‖x-a‖ ≤ δ := by
  classical
  obtain ⟨T,hT,hfin,hcover⟩ := (isCompact_closedBall (0 : Space d) D).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro a ha
    simpa only [mem_closedBall,dist_zero_right] using hT (hfin.mem_toFinset.mp ha)
  · intro x hx
    have hxc : x ∈ closedBall (0 : Space d) D := by simpa only [mem_closedBall,dist_zero_right] using hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hxc)
    refine ⟨a,hfin.mem_toFinset.mpr ha,?_⟩
    simpa only [mem_ball,dist_eq_norm] using hxa.le

theorem perpendicular_anchor_rounding {w x a y b : Space d} (hw : ‖w‖ = 1)
    {ε δ : ℝ} (hx : ‖perpendicularPart w (x-a)‖ ≤ ε)
    (hy : ‖perpendicularPart w (y-a)‖ ≤ ε) (hb : ‖y-b‖ ≤ δ) :
    ‖perpendicularPart w (x-b)‖ ≤ 2*ε+δ := by
  have he : perpendicularPart w (x-b) =
      (perpendicularPart w (x-a)-perpendicularPart w (y-a))+perpendicularPart w (y-b) := by
    simp only [perpendicularPart,inner_sub_right]
    module
  rw [he]
  exact (norm_add_le _ _).trans
    (((add_le_add (norm_sub_le _ _) (norm_perpendicularPart_le hw _)).trans
      (add_le_add (add_le_add hx hy) hb)).trans_eq (by ring))

theorem bounded_anchor_longitudinal (w : Sphere d) {x a : Space d} {D : ℝ}
    (hx : ‖x‖ ≤ D) (ha : ‖a‖ ≤ D) : |inner ℝ (w:Space d) (x-a)| ≤ 2*D := by
  calc
    _ ≤ ‖(w:Space d)‖*‖x-a‖ := abs_real_inner_le_norm _ _
    _ = ‖x-a‖ := by rw [sphere_norm,one_mul]
    _ ≤ ‖x‖+‖a‖ := norm_sub_le _ _
    _ ≤ 2*D := by linarith

theorem rounded_tube_cover (w : Sphere d) (E : Set (Space d))
    (S G : Finset (Space d)) {ε δ : ℝ}
    (hnet : ∀ x ∈ E, ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (hcover : ∀ x ∈ E, ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ J : Finset (Space d), J ⊆ G ∧ J.card ≤ S.card ∧
      ∀ x ∈ E, ∃ b ∈ J, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
  classical
  let P := fun a : Space d => ∃ y ∈ E, ‖perpendicularPart (w:Space d) (y-a)‖ ≤ ε
  have hround (a : Space d) (ha : P a) :
      ∃ b ∈ G, ∀ x ∈ E, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε →
        ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
    obtain ⟨y,hy,hya⟩ := ha
    obtain ⟨b,hb,hyb⟩ := hnet y hy
    exact ⟨b,hb,fun _ _ hx => perpendicular_anchor_rounding (sphere_norm w) hx hya hyb⟩
  let b : Space d → Space d := fun a => if ha : P a then (hround a ha).choose else 0
  let J := (S.filter P).image b
  refine ⟨J,?_,(Finset.card_image_le.trans (Finset.card_filter_le _ _)),?_⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_filter.mp ha).2
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.1
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    have hp : P a := ⟨x,hx,hxa⟩
    refine ⟨b a,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩,?_⟩
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.2 x hx hxa

end Falconer

end OAI
