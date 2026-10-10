import OAI.Geometry.CylinderCovering.Rational.Wedge
import OAI.Geometry.CylinderCovering.Convexity.RelaxedInversion
import OAI.Geometry.CylinderCovering.Rational.Lipschitz
import OAI.Geometry.CylinderCovering.Rational.GlobalInversionDefinitions

namespace OAI

open Set

namespace SlopeRational

theorem rational_wedge_isClosed : IsClosed wedge := by
  apply isClosed_le
  · fun_prop
  · unfold radius; fun_prop

theorem rational_wedge_convex : Convex ℝ wedge := by
  intro p hp q hq u v hu hv huv
  rw [mem_wedge_iff_walls] at hp hq ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · have h₁ := mul_nonneg hu hp.1
    have h₂ := mul_nonneg hv hq.1
    unfold radius at *
    nlinarith
  · have h₁ := mul_nonneg hu hp.2
    have h₂ := mul_nonneg hv hq.2
    unfold radius at *
    nlinarith

theorem global_wall_coefficients {d : ℝ} (hd : 0 < d) {p : Plane} (hp : p ∈ wedge) :
    |(2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2)| ≤ 1 / (4 * d) ∧
    |(-2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2)| ≤ 1 / (4 * d) := by
  have hr := radius_nonneg_of_mem_wedge hp
  have hD := denominator_pos_of_mem_wedge hd hp
  have hw := (mem_wedge_iff_walls p).mp hp
  have helper (Y : ℝ) (hl : -radius (p 1) / 2 ≤ Y) (hu : Y ≤ radius (p 1) / 2) :
      |(2 * Y + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2)| ≤ 1 / (4 * d) := by
    have hn : 0 ≤ 2 * Y + 2 * d + radius (p 1) := by linarith
    rw [abs_of_nonneg (div_nonneg hn (by positivity))]
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (radius (p 1) + d) ^ 2)
      (by positivity : 0 < 4 * d)).2
    nlinarith [mul_nonneg (show 0 ≤ radius (p 1) - 2 * Y by linarith) hd.le,
      mul_nonneg hr hD.le]
  exact ⟨helper (p 0) (by linarith) (by linarith),
    by simpa only [mul_neg, neg_mul] using helper (-p 0) (by linarith) (by linarith)⟩

theorem global_tiltedMap_mapsTo {d s : ℝ} (hd : 0 < d) (hs : |s| < d) :
    MapsTo (tiltedMap d s) wedge wedge := by
  intro p hp
  obtain ⟨hplus, hminus⟩ := global_wall_coefficients hd hp
  have hsmall : |s| * (1 / (4 * d)) < 1 := by
    rw [mul_one_div]
    apply (div_lt_one (by positivity : 0 < 4 * d)).2
    linarith [abs_nonneg s]
  have hpa : |s * ((2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hplus (abs_nonneg _)).trans_lt hsmall
  have hma : |s * ((-2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hminus (abs_nonneg _)).trans_lt hsmall
  rw [mem_wedge_iff_walls] at hp ⊢
  rw [tiltedMap_wall_plus d s (denominator_pos_of_mem_wedge hd
      ((mem_wedge_iff_walls p).mpr hp)).ne',
    tiltedMap_wall_minus d s (denominator_pos_of_mem_wedge hd
      ((mem_wedge_iff_walls p).mpr hp)).ne']
  constructor
  · exact mul_nonneg hp.1 (by linarith [(abs_lt.mp hpa).2])
  · exact mul_nonneg hp.2 (by linarith [(abs_lt.mp hma).1])

theorem rational_global_inverse_of_lipschitz {d L s : ℝ} (hd : 0 < d)
    (hL : 0 ≤ L)
    (hlip : ∀ p ∈ wedge, ∀ q ∈ wedge, ‖field d p - field d q‖ ≤ L * ‖p - q‖)
    (hsd : |s| < d) (hsL : |s| * L < 1) {y : Plane} (hy : y ∈ wedge) :
    ∃! p : Plane, p ∈ wedge ∧ tiltedMap d s p = y := by
  apply CylinderCovering.ThresholdInversion.existsUnique_inverse_on_convex
    rational_wedge_isClosed.isComplete rational_wedge_convex
    (mul_nonneg (abs_nonneg s) hL) hsL (g := fun p => s • field d p) ?_ ?_ hy
  · intro p hp q hq
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc
      |s| * ‖field d p - field d q‖ ≤ |s| * (L * ‖p - q‖) :=
        mul_le_mul_of_nonneg_left (hlip p hp q hq) (abs_nonneg _)
      _ = |s| * L * ‖p - q‖ := by ring
  · intro p hp
    have h := global_tiltedMap_mapsTo hd (s := -s) (by simpa using hsd) hp
    simpa only [tiltedMap, neg_smul, sub_eq_add_neg] using h

theorem rational_global_inverse {d s : ℝ} (hd : 0 < d) (hs : |s| < d / 4)
    {y : Plane} (hy : y ∈ wedge) :
    ∃! p : Plane, p ∈ wedge ∧ tiltedMap d s p = y := by
  apply rational_global_inverse_of_lipschitz hd (L := 2 / d) (by positivity)
  · intro p hp q hq
    have h := (field_lipschitzOn_wedge hd).dist_le_mul p hp q hq
    change dist (field d p) (field d q) ≤ (2 / d) * dist p q at h
    simpa only [dist_eq_norm] using h
  · linarith
  · rw [show |s| * (2 / d) = (2 * |s|) / d by ring]
    apply (div_lt_one hd).2
    linarith
  · exact hy

theorem globalWedgeInversion_main : GlobalWedgeInversionStatement := by
  intro d hd
  refine ⟨d / 4, by positivity, ?_⟩
  intro s hs
  have hmap := global_tiltedMap_mapsTo hd (s := s) (by linarith)
  refine ⟨hmap, ?_, ?_⟩
  · intro p hp q hq hpq
    have h := rational_global_inverse hd hs (hmap hp)
    exact h.unique ⟨hp, rfl⟩ ⟨hq, hpq.symm⟩
  · intro y hy
    obtain ⟨p, hp, _⟩ := rational_global_inverse hd hs hy
    exact ⟨p, hp.1, hp.2⟩

end SlopeRational

end OAI
