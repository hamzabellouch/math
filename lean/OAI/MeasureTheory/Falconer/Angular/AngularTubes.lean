import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

theorem perpendicular_direction_two_caps {w v : E} (hw : ‖w‖ = 1)
    (hv : v ≠ 0) {W : ℝ} (htube : ‖perpendicularPart w v‖ ≤ W) :
    ‖w-‖v‖⁻¹ • v‖ ≤ 2*W/‖v‖ ∨ ‖w-(-‖v‖⁻¹ • v)‖ ≤ 2*W/‖v‖ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
  have hpu : ‖perpendicularPart w u‖ ≤ W/‖v‖ := by
    dsimp [u]
    rw [perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left htube (inv_nonneg.mpr hvp.le)
  have hscale : 2*‖perpendicularPart w u‖ ≤ 2*W/‖v‖ := by
    calc
      _ ≤ 2*(W/‖v‖) := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ = _ := by ring
  rcases le_total 0 (inner ℝ w u) with hi | hi
  · exact Or.inl ((unit_close_of_perpendicular hw hu hi).trans hscale)
  · have hneg : perpendicularPart w (-u) = -perpendicularPart w u := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    have hh := unit_close_of_perpendicular hw (by simpa only [norm_neg] using hu)
      (show 0 ≤ inner ℝ w (-u) by rw [inner_neg_right]; linarith)
    rw [hneg,norm_neg] at hh
    right
    simpa only [u,neg_smul] using hh.trans hscale

theorem perpendicular_direction_measure {d : ℕ} (ν : Measure (Sphere d))
    {v : Space d} (hv : v ≠ 0) {W L s : ℝ} (hW : 0 < W)
    (hball : ∀ x : Space d, ν {w : Sphere d | dist (w:Space d) x < 3*W/‖v‖} ≤
      ENNReal.ofReal (L*(3*W/‖v‖)^s)) :
    ν {w : Sphere d | ‖perpendicularPart (w:Space d) v‖ ≤ W} ≤
      2*ENNReal.ofReal (L*(3*W/‖v‖)^s) := by
  let u := ‖v‖⁻¹ • v
  have hsmall : 2*W/‖v‖ < 3*W/‖v‖ := by
    apply (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hv)).mpr
    linarith
  have hsub : {w : Sphere d | ‖perpendicularPart (w:Space d) v‖ ≤ W} ⊆
      {w : Sphere d | dist (w:Space d) u < 3*W/‖v‖} ∪
      {w : Sphere d | dist (w:Space d) (-u) < 3*W/‖v‖} := by
    intro w hw
    rcases perpendicular_direction_two_caps (sphere_norm w) hv hw with h | h
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq,dist_eq_norm,u] using h.trans_lt hsmall)
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,dist_eq_norm,u,neg_smul] using h.trans_lt hsmall)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add (hball u) (hball (-u))).trans_eq (by ring)))

end Falconer

end OAI
