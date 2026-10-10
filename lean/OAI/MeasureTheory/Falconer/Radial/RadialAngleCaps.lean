import OAI.MeasureTheory.Falconer.Angular.GnomonicTripleAngle

namespace OAI

/-! # Two radial caps control near-collinear affine triples -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem displacementAngle_measurable (p q : Space n) :
    Measurable (displacementAngle p q) := by
  unfold displacementAngle perpendicularPart NormedSpace.normalize
  fun_prop

theorem displacementAngle_two_caps (p q z : Space n) (hq : q ≠ p) (hz : z ≠ p)
    {r : ℝ} (hr : 0 < r) (ha : displacementAngle p q z ≤ r) :
    dist (normalize (z-p)) (normalize (q-p)) < 3*r ∨
      dist (normalize (z-p)) (-normalize (q-p)) < 3*r := by
  let u := normalize (q-p)
  let v := normalize (z-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hv : ‖v‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  rcases perpendicular_direction_two_caps hu hv0 ha with hl | hr'
  · left
    have hh : ‖u-v‖ ≤ 2*r := by
      simpa only [hv,inv_one,one_smul,div_one] using hl
    change ‖v-u‖ < 3*r
    rw [norm_sub_rev]
    linarith
  · right
    have hh : ‖u+v‖ ≤ 2*r := by
      simpa only [hv,inv_one,neg_smul,one_smul,div_one,sub_neg_eq_add] using hr'
    change ‖v-(-u)‖ < 3*r
    rw [sub_neg_eq_add,add_comm]
    linarith

theorem radial_angle_sublevel (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {r K ℓ : ℝ} (hr : 0 < r)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ≤
        ENNReal.ofReal (K*(3*r)^ℓ)) :
    μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ≤
      2*ENNReal.ofReal (K*(3*r)^ℓ) := by
  let u := normalize (q-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hsub : {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ⊆
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ∪
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) (-u) < 3*r} := by
    rintro z ⟨hz,ha⟩
    rcases displacementAngle_two_caps p q z hq (hdiag z hz) hr ha with h | h
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  have hh := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (hcap u hu) (hcap (-u) (by simpa only [norm_neg] using hu))))
  exact hh.trans_eq (by ring)

end Falconer

end OAI
