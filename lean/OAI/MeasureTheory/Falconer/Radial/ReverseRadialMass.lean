import OAI.MeasureTheory.Falconer.Radial.ReverseRadialGeometry

namespace OAI

/-! # Original reverse cap bounds control radial collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_mass (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n) (hy : y ≠ z)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 0 < D) (hδ : 0 < δ)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < 3*(D*δ/‖y-z‖)} ≤
        ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      2*ENNReal.ofReal (K*(3*(D*δ/‖y-z‖))^q) := by
  have hr : 0 < D*δ/‖y-z‖ := div_pos (mul_pos hD hδ)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hy))
  apply (measure_mono (show
    {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ⊆
      {x | (z,x) ∈ G ∧ displacementAngle z y x ≤ D*δ/‖y-z‖} from ?_)).trans
    (radial_angle_sublevel ν G z y hy hdiag hr hcap)
  rintro x ⟨hx,hclose⟩
  exact ⟨hx,reverse_radial_collision_angle x z y (Ne.symm (hdiag x hx)) hy (hbound x hx) hclose⟩

end Falconer

end OAI
