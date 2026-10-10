import OAI.Geometry.CylinderCovering.Radial.Assembly

namespace OAI

noncomputable section
open Set

namespace CylinderCovering.RadialRiemann

lemma weighted_square_collar_bounds {r M K d W : ℝ}
    (hr : 0 ≤ r) (hrM : r ≤ M) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hW : 0 ≤ W) (hW1 : W ≤ 1) :
    0 ≤ ((r + K * d)^2 - r^2) * W ∧
      ((r + K * d)^2 - r^2) * W ≤ 2 * M * K * d + K^2 * d^2 := by
  have hinc : (r + K * d)^2 - r^2 = 2 * r * K * d + K^2 * d^2 := by ring
  have h0 : 0 ≤ 2 * r * K * d + K^2 * d^2 := by positivity
  have hle : 2 * r * K * d + K^2 * d^2 ≤
      2 * M * K * d + K^2 * d^2 := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrM (show (0 : ℝ) ≤ 2 by norm_num)) hK) hd) le_rfl
  rw [hinc]
  exact ⟨mul_nonneg h0 hW,
    (mul_le_of_le_one_right h0 hW1).trans hle⟩

lemma step_le_length {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    step a b N ≤ b - a := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [step, div_le_iff₀ hn0]
  nlinarith [sub_pos.mpr hab]

theorem collarSum_sub_zero_bounds {a b M K : ℝ} (hab : a < b)
    {R W : ℝ → ℝ} (hR : ContinuousOn R (Icc a b))
    (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t) (hM : ∀ t ∈ Icc a b, R t ≤ M)
    (hK : 0 ≤ K) {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (hW0 : ∀ i, 0 ≤ W (tag i)) (hW1 : ∀ i, W (tag i) ≤ 1) :
    0 ≤ collarSum R W K a b N tag - collarSum R W 0 a b N tag ∧
      collarSum R W K a b N tag - collarSum R W 0 a b N tag ≤
        (b - a) * (2 * M * K * step a b N + K^2 * (step a b N)^2) := by
  have hd := (step_pos hab hN).le
  have hcell (i : Fin N) := weighted_square_collar_bounds
    (capMax_nonneg hab hR hR0 i)
    (capMax_le hab hR i (fun t ht => hM t (cell_subset hab i ht)))
    hK hd (hW0 i) (hW1 i)
  have heq : collarSum R W K a b N tag - collarSum R W 0 a b N tag =
      ∑ i : Fin N, step a b N *
        (((capMax R a b N i + K * step a b N)^2 - (capMax R a b N i)^2) *
          W (tag i)) := by
    simp only [collarSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg hd (hcell i).1)
  · calc
      _ ≤ ∑ _i : Fin N, step a b N *
          (2 * M * K * step a b N + K^2 * (step a b N)^2) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcell i).2 hd)
      _ = (b - a) * (2 * M * K * step a b N + K^2 * (step a b N)^2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, count_step hN]

theorem collarSum_sub_zero_le_div {a b M K : ℝ} (hab : a < b)
    {R W : ℝ → ℝ} (hR : ContinuousOn R (Icc a b))
    (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t) (hM : ∀ t ∈ Icc a b, R t ≤ M)
    (hK : 0 ≤ K) {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (hW0 : ∀ i, 0 ≤ W (tag i)) (hW1 : ∀ i, W (tag i) ≤ 1) :
    collarSum R W K a b N tag - collarSum R W 0 a b N tag ≤
      (b - a)^2 * (2 * M * K + K^2 * (b - a)) / N := by
  have hd := (step_pos hab hN).le
  have hdl := step_le_length hab hN
  have hsq : (step a b N)^2 ≤ (b - a) * step a b N := by
    nlinarith
  calc
    _ ≤ (b - a) * (2 * M * K * step a b N + K^2 * (step a b N)^2) :=
      (collarSum_sub_zero_bounds hab hR hR0 hM hK hN tag hW0 hW1).2
    _ ≤ (b - a) * (2 * M * K * step a b N + K^2 * ((b - a) * step a b N)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (sq_nonneg K)))
        (sub_nonneg.mpr hab.le)
    _ = (b - a)^2 * (2 * M * K + K^2 * (b - a)) / N := by
      unfold step
      ring

end CylinderCovering.RadialRiemann

namespace CylinderCovering.RadialSweep

lemma projectionWeight_bounds (x : Space) :
    0 ≤ 1 / Real.sqrt (1 + ‖x‖^2) ∧
      1 / Real.sqrt (1 + ‖x‖^2) ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 1 + ‖x‖^2 := le_add_of_nonneg_right (sq_nonneg ‖x‖)
  have hs : 1 ≤ Real.sqrt (1 + ‖x‖^2) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hbase
  refine ⟨div_nonneg zero_le_one (Real.sqrt_nonneg _), ?_⟩
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).2
  simpa only [one_mul] using hs

lemma sum_frozenArea_eq_collarSum (D : Data) (N : ℕ) (tag : Fin N → ℝ) :
    (∑ i : Fin N, frozenArea D N tag i) = kappa D / 2 *
      RadialRiemann.collarSum D.R
        (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2))
        (radialError D + collar D) D.α D.β N tag := by
  simp only [frozenArea, RadialRiemann.collarSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem frozenCylinder_collar_bounds (D : Data) {M : ℝ}
    (hM : ∀ t ∈ Icc D.α D.β, D.R t ≤ M)
    {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    0 ≤ TriangularCovering.totalArea (frozenCylinder D N tag htag) -
      kappa D / 2 * RadialRiemann.collarSum D.R
        (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag ∧
    TriangularCovering.totalArea (frozenCylinder D N tag htag) -
      kappa D / 2 * RadialRiemann.collarSum D.R
        (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag ≤
      kappa D / 2 * (D.β - D.α) *
        (2 * M * (radialError D + collar D) * RadialRiemann.step D.α D.β N +
          (radialError D + collar D)^2 * (RadialRiemann.step D.α D.β N)^2) := by
  have hK := add_nonneg (radialError_nonneg D) (collar_pos D).le
  have h := RadialRiemann.collarSum_sub_zero_bounds D.interval_nonempty
    (W := fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2))
    D.cap_continuous D.cap_nonneg hM hK hN tag
    (fun i => (projectionWeight_bounds (D.w (tag i))).1)
    (fun i => (projectionWeight_bounds (D.w (tag i))).2)
  have hκ : 0 ≤ kappa D / 2 := div_nonneg (kappa_nonneg D) (by norm_num)
  unfold TriangularCovering.totalArea
  simp only [frozenCylinder_area, sum_frozenArea_eq_collarSum]
  rw [← mul_sub]
  refine ⟨mul_nonneg hκ h.1, ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h.2 hκ

theorem frozenCylinder_collar_le_div (D : Data) {M : ℝ}
    (hM : ∀ t ∈ Icc D.α D.β, D.R t ≤ M)
    {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    TriangularCovering.totalArea (frozenCylinder D N tag htag) -
      kappa D / 2 * RadialRiemann.collarSum D.R
        (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag ≤
      (kappa D / 2 * (D.β - D.α)^2 *
        (2 * M * (radialError D + collar D) +
          (radialError D + collar D)^2 * (D.β - D.α))) / N := by
  have hK := add_nonneg (radialError_nonneg D) (collar_pos D).le
  have h := RadialRiemann.collarSum_sub_zero_le_div D.interval_nonempty
    (W := fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2))
    D.cap_continuous D.cap_nonneg hM hK hN tag
    (fun i => (projectionWeight_bounds (D.w (tag i))).1)
    (fun i => (projectionWeight_bounds (D.w (tag i))).2)
  have hκ : 0 ≤ kappa D / 2 := div_nonneg (kappa_nonneg D) (by norm_num)
  unfold TriangularCovering.totalArea
  simp only [frozenCylinder_area, sum_frozenArea_eq_collarSum]
  rw [← mul_sub]
  simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left h hκ

theorem frozenCylinder_collar_uniform (D : Data) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ tag : Fin N → ℝ,
      ∀ htag : RadialRiemann.IsTagged D.α D.β N tag,
      0 ≤ TriangularCovering.totalArea (frozenCylinder D N tag htag) -
        kappa D / 2 * RadialRiemann.collarSum D.R
          (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag ∧
      TriangularCovering.totalArea (frozenCylinder D N tag htag) -
        kappa D / 2 * RadialRiemann.collarSum D.R
          (fun t => 1 / Real.sqrt (1 + ‖D.w t‖^2)) 0 D.α D.β N tag ≤ C / N := by
  let M := sSup (D.R '' Icc D.α D.β)
  have hM : ∀ t ∈ Icc D.α D.β, D.R t ≤ M := by
    intro t ht
    exact le_csSup (isCompact_Icc.bddAbove_image D.cap_continuous) ⟨t, ht, rfl⟩
  have hM0 : 0 ≤ M := (D.cap_nonneg D.α ⟨le_rfl, D.interval_nonempty.le⟩).trans
    (hM D.α ⟨le_rfl, D.interval_nonempty.le⟩)
  have hK := add_nonneg (radialError_nonneg D) (collar_pos D).le
  have hκ := kappa_nonneg D
  have hlen := sub_pos.mpr D.interval_nonempty
  refine ⟨kappa D / 2 * (D.β - D.α)^2 *
    (2 * M * (radialError D + collar D) +
      (radialError D + collar D)^2 * (D.β - D.α)), by positivity, ?_⟩
  intro N hN tag htag
  exact ⟨(frozenCylinder_collar_bounds D hM hN tag htag).1,
    frozenCylinder_collar_le_div D hM hN tag htag⟩

end CylinderCovering.RadialSweep

end

end OAI
