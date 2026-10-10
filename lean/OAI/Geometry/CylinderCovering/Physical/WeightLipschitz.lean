import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
namespace RuledApproximation

lemma inverse_difference_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |1 / a - 1 / b| ≤ |a - b| := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 1 ≤ a * b := by nlinarith
  have hid : 1 / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).2
  nlinarith only [mul_nonneg (abs_nonneg (a - b)) (sub_nonneg.mpr hab)]

lemma physicalDirection_norm_one_le (h : ℝ) (g : Plane) :
    1 ≤ ‖physicalDirection h g‖ := by
  have heq := physicalDirection_norm_sq h g
  have hn := norm_nonneg (physicalDirection h g)
  nlinarith [sq_nonneg (g 0), mul_nonneg (sq_nonneg h) (sq_nonneg (g 1))]

lemma physicalDirection_difference_bound (h : ℝ) (u v : Plane) :
    ‖physicalDirection h u - physicalDirection h v‖ ≤ max 1 |h| * ‖u - v‖ := by
  have hc1 : (1 : ℝ) ≤ max 1 |h| := le_max_left _ _
  have hc0 : (0 : ℝ) ≤ max 1 |h| := le_trans (by norm_num) hc1
  have hch : |h| ≤ max 1 |h| := le_max_right _ _
  have hc2 : 1 ≤ (max 1 |h|) ^ 2 := by nlinarith
  have hh2 : h ^ 2 ≤ (max 1 |h|) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg h) hc0).mpr hch
    simpa only [sq_abs] using hs
  have heq : physicalDirection h u - physicalDirection h v =
      vec3 0 (u 0 - v 0) (h * (u 1 - v 1)) := by
    ext i
    fin_cases i <;> simp [physicalDirection, vec3]
    ring
  have hnorm : ‖physicalDirection h u - physicalDirection h v‖ ^ 2 =
      (u 0 - v 0) ^ 2 + h ^ 2 * (u 1 - v 1) ^ 2 := by
    rw [heq, norm_vec3_sq]
    ring
  have huv : ‖u - v‖ ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 := by
    simpa only [PiLp.sub_apply] using norm_plane_sq (u - v)
  have h1 := mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg (u 0 - v 0))
  have h2 := mul_nonneg (sub_nonneg.mpr hh2) (sq_nonneg (u 1 - v 1))
  have hn0 := norm_nonneg (physicalDirection h u - physicalDirection h v)
  have hn1 := mul_nonneg hc0 (norm_nonneg (u - v))
  nlinarith only [hnorm, huv, h1, h2, hn0, hn1]

theorem physicalWeight_difference_le (h : ℝ) (u v : Plane) :
    |physicalWeight h u - physicalWeight h v| ≤ max 1 |h| * ‖u - v‖ := by
  rw [physicalWeight_eq_inv_norm, physicalWeight_eq_inv_norm]
  exact (inverse_difference_le (physicalDirection_norm_one_le h u)
    (physicalDirection_norm_one_le h v)).trans
      ((abs_norm_sub_norm_le _ _).trans (physicalDirection_difference_bound h u v))

theorem physicalWeight_lipschitzWith (h : ℝ) :
    LipschitzWith ⟨max 1 |h|, le_trans (by norm_num) (le_max_left _ _)⟩ (physicalWeight h) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (physicalWeight h u) (physicalWeight h v) ≤ max 1 |h| * dist u v
  rw [Real.dist_eq, dist_eq_norm]
  exact physicalWeight_difference_le h u v

lemma physicalWeight_le_one (h : ℝ) (g : Plane) : physicalWeight h g ≤ 1 := by
  rw [physicalWeight_eq_inv_norm]
  exact (div_le_one (physicalDirection_norm_pos h g)).mpr (physicalDirection_norm_one_le h g)

lemma affine_physicalWeight_error {h M C δ : ℝ} {q l b : Plane}
    (A : Plane →L[ℝ] Plane) (hM : 0 ≤ M) (_ : 0 ≤ C) (_ : 0 ≤ δ)
    (hA : ‖A‖ ≤ M) (hl : ‖l - b‖ ≤ C * δ) :
    |physicalWeight h (q + A (l - b)) - physicalWeight h q| ≤
      max 1 |h| * M * C * δ := by
  have hH : 0 ≤ max 1 |h| := le_trans (by norm_num) (le_max_left _ _)
  calc
    |physicalWeight h (q + A (l - b)) - physicalWeight h q| ≤
        max 1 |h| * ‖q + A (l - b) - q‖ := physicalWeight_difference_le _ _ _
    _ = max 1 |h| * ‖A (l - b)‖ := by rw [add_sub_cancel_left]
    _ ≤ max 1 |h| * (‖A‖ * ‖l - b‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) hH
    _ ≤ max 1 |h| * (M * (C * δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hA hl (norm_nonneg _) hM) hH
    _ = max 1 |h| * M * C * δ := by ring

end RuledApproximation

namespace NilpotentRate

theorem collar_area_bound {δ R K : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hRK : R ≤ K * δ ^ 2) :
    (δ + 2 * R + 2 * Real.sqrt 2 * δ ^ 2) ^ 2 ≤
      δ ^ 2 + (4 * (K + Real.sqrt 2) + 4 * (K + Real.sqrt 2) ^ 2) * δ ^ 3 := by
  let L := 2 * (K + Real.sqrt 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbase : 0 ≤ δ + 2 * R + 2 * Real.sqrt 2 * δ ^ 2 := by positivity
  have hbase' : δ + 2 * R + 2 * Real.sqrt 2 * δ ^ 2 ≤ δ + L * δ ^ 2 := by
    dsimp [L]
    nlinarith only [hRK]
  have hsq := (sq_le_sq₀ hbase (by positivity : 0 ≤ δ + L * δ ^ 2)).mpr hbase'
  have hpow := mul_nonneg (sub_nonneg.mpr hδ1) (pow_nonneg hδ 3)
  have herr := mul_nonneg (sq_nonneg L) hpow
  dsimp [L] at hsq herr
  nlinarith only [hsq, herr]

theorem weighted_cell_bound {δ A J C W cost : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (_ : 0 ≤ A) (hJ : 0 ≤ J) (hJ1 : J ≤ 1)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (harea : A ≤ δ ^ 2 + C * δ ^ 3)
    (hcost : cost ≤ A * (J + W * δ)) :
    cost ≤ δ ^ 2 * J + (C + W + C * W) * δ ^ 3 := by
  have hweight : 0 ≤ J + W * δ := by positivity
  have h1 := mul_le_mul_of_nonneg_right harea hweight
  have h2 := mul_nonneg (mul_nonneg hC (pow_nonneg hδ 3)) (sub_nonneg.mpr hJ1)
  have h3 := mul_nonneg (mul_nonneg hC hW)
    (mul_nonneg (sub_nonneg.mpr hδ1) (pow_nonneg hδ 3))
  nlinarith only [hcost, h1, h2, h3]

theorem sum_cell_errors {ι : Type*} [Fintype ι] {δ B C : ℝ}
    (cost weight : ι → ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) * δ ^ 2 ≤ B)
    (hcell : ∀ i, cost i ≤ δ ^ 2 * weight i + C * δ ^ 3) :
    ∑ i, cost i ≤ (∑ i, δ ^ 2 * weight i) + B * C * δ := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcell i)
  have hmul := mul_le_mul_of_nonneg_right hcount (mul_nonneg hC hδ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith only [hs, hmul]

end NilpotentRate

end

end OAI
