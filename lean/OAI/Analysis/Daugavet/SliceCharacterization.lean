import OAI.Analysis.Daugavet.ExactModuli

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma normalized_functional_slice_nonempty (ell : X →L[ℝ] ℝ) (hell : ‖ell‖ = 1)
    {η : ℝ} (hη : 0 < η) : ∃ y : X, ‖y‖ ≤ 1 ∧ 1 - η < ell y := by
  obtain ⟨u, hu, hval⟩ := ell.exists_lt_apply_of_lt_opNorm
    (show 1 - η < ‖ell‖ by rw [hell]; linarith)
  rw [Real.norm_eq_abs] at hval
  by_cases hs : 0 ≤ ell u
  · exact ⟨u, hu.le, by rwa [abs_of_nonneg hs] at hval⟩
  · refine ⟨-u, by simpa using hu.le, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hs)] at hval
    simpa only [map_neg] using hval

/-- Converse slice characterization, needed for the explicitly constructed example. -/
theorem unitSlice_daugavet [Nontrivial X] (hsp : UnitSliceProperty X) : Daugavet X := by
  intro ell v
  by_cases he0 : ell = 0
  · simp [he0, ContinuousLinearMap.norm_id]
  by_cases hv0 : v = 0
  · simp [hv0, ContinuousLinearMap.norm_id]
  have he : 0 < ‖ell‖ := norm_pos_iff.mpr he0
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let f : X →L[ℝ] ℝ := ‖ell‖⁻¹ • ell
  have hf : ‖f‖ = 1 := norm_smul_inv_norm he0
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hv0
  let a := ‖ell‖ * ‖v‖
  have ha : 0 < a := mul_pos he hv
  let T : X →L[ℝ] X := ContinuousLinearMap.id ℝ X + ell.smulRight v
  have hnrank : ‖ell.smulRight v‖ = a := ContinuousLinearMap.norm_smulRight_apply _ _
  apply le_antisymm
  · have hb := norm_add_le (ContinuousLinearMap.id ℝ X) (ell.smulRight v)
    simpa only [ContinuousLinearMap.norm_id] using hb
  · rw [hnrank]
    change 1 + a ≤ ‖T‖
    apply le_of_forall_pos_le_add
    intro δ hδ
    let η := min (1 / 2 : ℝ) (δ / (4 * (a + 1)))
    have hη : 0 < η := by dsimp [η]; positivity
    have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hηδ : η * (4 * (a + 1)) ≤ δ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    obtain ⟨y, hy, hfy, hfar⟩ := hsp w hw f (1 - η)
      (normalized_functional_slice_nonempty f hf hη) η hη
    obtain ⟨φ, hφ, hφsum⟩ := exists_dual_vector'' ℝ (w + y)
    change φ (w + y) = ‖w + y‖ at hφsum
    rw [map_add] at hφsum
    have hφw : φ w ≤ 1 := by simpa only [hw] using dual_apply_le_norm φ hφ w
    have hφy : φ y ≤ 1 := by simpa only [hy] using dual_apply_le_norm φ hφ y
    have hwlo : 1 - η ≤ φ w := by linarith
    have hylo : 1 - η ≤ φ y := by linarith
    have hfylo : 1 - η ≤ f y := hfy.le
    have hprod : (1 - η) ^ 2 ≤ f y * φ w := by
      have hp := mul_le_mul hfylo hwlo (by linarith : 0 ≤ 1 - η) (by linarith : 0 ≤ f y)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod ha.le
    have heval : ell y = ‖ell‖ * f y := by
      change ell y = ‖ell‖ * (‖ell‖⁻¹ * ell y)
      rw [← mul_assoc, mul_inv_cancel₀ he.ne', one_mul]
    have hvid : v = ‖v‖ • w := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
    have hφv : φ v = ‖v‖ * φ w := by conv_lhs => rw [hvid]; rw [map_smul, smul_eq_mul]
    have hTφ : φ (T y) = φ y + a * (f y * φ w) := by
      change φ (y + ell y • v) = _
      rw [map_add, map_smul, smul_eq_mul, heval, hφv]
      dsimp [a]
      ring
    have hbound := dual_apply_le_norm φ hφ (T y)
    have hop := T.le_opNorm y
    rw [hy, mul_one] at hop
    rw [hTφ] at hbound
    nlinarith [mul_nonneg ha.le (sq_nonneg η)]

end ExactModuli

end

end OAI
