import OAI.MeasureTheory.Falconer.Radial.ReverseRadialGeometry

namespace OAI

/-! # Robust tube covers under small unoriented changes of direction -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hdir : ‖w-v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hdir
  have he := perpendicularPart_direction_error hv hw z
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart v z) (perpendicularPart w z) 0
  simp only [sub_zero] at htri
  have hdir' : ‖v-w‖ ≤ η := by simpa only [norm_sub_rev] using hdir
  calc
    _ ≤ ‖perpendicularPart v z-perpendicularPart w z‖+‖perpendicularPart w z‖ := htri
    _ ≤ 2*‖v-w‖*‖z‖+r := add_le_add he htube
    _ ≤ 2*η*L+r := by gcongr
    _ = _ := by ring

theorem unoriented_tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  rcases hdir with hdir | hdir
  · exact tube_direction_point_bound hw hv hdir hz htube
  · have hh := tube_direction_point_bound hw (show ‖-v‖ = 1 by simpa using hv)
      (show ‖w-(-v)‖ ≤ η by simpa only [sub_neg_eq_add] using hdir) hz htube
    simpa only [perpendicularPart_neg_left] using hh

theorem tube_cover_direction_transport (μ : Measure (Space d))
    {w v : Space d} {D B η r : ℝ} (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (S : Finset (Space d)) (hS : ∀ a ∈ S, ‖a‖ ≤ B) :
    μ {x | ∃ a ∈ S, ‖perpendicularPart w (x-a)‖ ≤ r} ≤
      μ {x | ∃ a ∈ S, ‖perpendicularPart v (x-a)‖ ≤ r+2*η*(D+B)} := by
  apply measure_mono_ae
  filter_upwards [hμ] with x hx
  rintro ⟨a,ha,htube⟩
  refine ⟨a,ha,unoriented_tube_direction_point_bound hw hv hdir ?_ htube⟩
  exact (norm_sub_le x a).trans (add_le_add hx (hS a ha))

end Falconer

end OAI
