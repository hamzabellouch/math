import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialRiccati
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! # Bounded normalized inverse for the actual outgoing value matrix

The two physical channel factors have the same modulus. Consequently
conjugation by their diagonal does not enlarge an operator norm. No
derivative of the inverse matrix is used in the high-derivative estimate.
-/

open Set Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousTwoColumns_norm (u v : V) :
    ‖spectralTwoColumns u v‖ ≤ ‖u‖ + ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [spectralTwoColumns_apply]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul]
  calc
    _ ≤ ‖w‖ * ‖u‖ + ‖w‖ * ‖v‖ := add_le_add
      (mul_le_mul_of_nonneg_right (norm_fst_le w) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_snd_le w) (norm_nonneg _))
    _ = _ := by ring

noncomputable def homogeneousDiagonal (a b : ℂ) : End :=
  spectralTwoColumns (a, 0) (0, b)

theorem homogeneousDiagonal_apply (a b : ℂ) (w : V) :
    homogeneousDiagonal a b w = (a * w.1, b * w.2) := by
  apply Prod.ext <;>
    simp only [homogeneousDiagonal, spectralTwoColumns_apply, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero, zero_add, mul_comm]

theorem homogeneousDiagonal_norm (a b : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (w : V) :
    ‖homogeneousDiagonal a b w‖ = ρ * ‖w‖ := by
  rw [homogeneousDiagonal_apply]
  simp only [Prod.norm_def, norm_mul, ha, hb]
  exact (mul_max_of_nonneg _ _ hρ).symm

theorem homogeneousDiagonal_inv_apply (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (w : V) :
    homogeneousDiagonal a⁻¹ b⁻¹ (homogeneousDiagonal a b w) = w := by
  simp only [homogeneousDiagonal_apply, ← mul_assoc, inv_mul_cancel₀ ha,
    inv_mul_cancel₀ hb, one_mul, Prod.mk.eta]

theorem homogeneousDiagonal_columns (a b : ℂ) (u v : V) :
    spectralTwoColumns (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) =
      homogeneousDiagonal a b * spectralTwoColumns u v := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [spectralTwoColumns_apply, mul_apply_eq_comp, map_add, map_smul]

theorem homogeneousDiagonal_det (a b : ℂ) (u v : V) :
    spectralValueDet (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) =
      a * b * spectralValueDet u v := by
  simp only [homogeneousDiagonal_apply, spectralValueDet]
  ring

theorem homogeneousDiagonal_valueInverse (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u v : V) (hd : spectralValueDet u v ≠ 0) :
    spectralValueInverse (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) =
      spectralValueInverse u v * homogeneousDiagonal a⁻¹ b⁻¹ := by
  have hdet : spectralValueDet (homogeneousDiagonal a b u)
      (homogeneousDiagonal a b v) ≠ 0 := by
    rw [homogeneousDiagonal_det]
    exact mul_ne_zero (mul_ne_zero ha hb) hd
  apply ContinuousLinearMap.ext
  intro w
  let z := spectralValueInverse (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) w
  have hz : homogeneousDiagonal a b (spectralTwoColumns u v z) = w := by
    rw [← mul_apply_eq_comp, ← homogeneousDiagonal_columns]
    exact spectralTwoColumns_apply_inverse _ _ w hdet
  have h := congrArg (homogeneousDiagonal a⁻¹ b⁻¹) hz
  rw [homogeneousDiagonal_inv_apply a b ha hb] at h
  change z = spectralValueInverse u v (homogeneousDiagonal a⁻¹ b⁻¹ w)
  rw [← h, spectralValueInverse_apply_columns u v z hd]

theorem homogeneousDiagonal_conjugate_norm (a b : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (M : End) :
    ‖homogeneousDiagonal a b * M * homogeneousDiagonal a⁻¹ b⁻¹‖ ≤ ‖M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
  intro w
  have hia : ‖a⁻¹‖ = ρ⁻¹ := by rw [norm_inv, ha]
  have hib : ‖b⁻¹‖ = ρ⁻¹ := by rw [norm_inv, hb]
  simp only [mul_apply_eq_comp]
  rw [homogeneousDiagonal_norm a b ρ hρ.le ha hb]
  calc
    _ ≤ ρ * (‖M‖ * ‖homogeneousDiagonal a⁻¹ b⁻¹ w‖) :=
      mul_le_mul_of_nonneg_left (M.le_opNorm _) hρ.le
    _ = ‖M‖ * ‖w‖ := by
      rw [homogeneousDiagonal_norm a⁻¹ b⁻¹ ρ⁻¹ (inv_nonneg.mpr hρ.le) hia hib]
      field_simp

theorem homogeneousDiagonal_remainder_norm (a b : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (u v p q : V)
    (hd : spectralValueDet u v ≠ 0) :
    ‖spectralTwoColumns (homogeneousDiagonal a b p) (homogeneousDiagonal a b q) *
      spectralValueInverse (homogeneousDiagonal a b u) (homogeneousDiagonal a b v)‖ ≤
      ‖spectralTwoColumns p q‖ * ‖spectralValueInverse u v‖ := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (ha.symm ▸ hρ)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hb.symm ▸ hρ)
  rw [homogeneousDiagonal_columns,
    homogeneousDiagonal_valueInverse a b ha0 hb0 u v hd]
  calc
    _ = ‖homogeneousDiagonal a b *
        (spectralTwoColumns p q * spectralValueInverse u v) *
          homogeneousDiagonal a⁻¹ b⁻¹‖ := by simp only [mul_assoc]
    _ ≤ ‖spectralTwoColumns p q * spectralValueInverse u v‖ :=
      homogeneousDiagonal_conjugate_norm a b ρ hρ ha hb _
    _ ≤ _ := norm_mul_le _ _

theorem homogeneousDiagonal_commute (a b c d : ℂ) :
    Commute (homogeneousDiagonal a b) (homogeneousDiagonal c d) := by
  change homogeneousDiagonal a b * homogeneousDiagonal c d =
    homogeneousDiagonal c d * homogeneousDiagonal a b
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext <;> simp only [mul_apply_eq_comp, homogeneousDiagonal_apply]
  all_goals ring

theorem homogeneousDiagonal_robin_difference (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u v du dv : V) (hd : spectralValueDet u v ≠ 0) (K : End)
    (hK : Commute K (homogeneousDiagonal a b)) :
    spectralRobinOperator (homogeneousDiagonal a b u) (homogeneousDiagonal a b v)
        (homogeneousDiagonal a b (K u + du)) (homogeneousDiagonal a b (K v + dv)) - K =
      homogeneousDiagonal a b * (spectralTwoColumns du dv * spectralValueInverse u v) *
        homogeneousDiagonal a⁻¹ b⁻¹ := by
  have hdet : spectralValueDet (homogeneousDiagonal a b u)
      (homogeneousDiagonal a b v) ≠ 0 := by
    rw [homogeneousDiagonal_det]
    exact mul_ne_zero (mul_ne_zero ha hb) hd
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := homogeneousTwoColumns_surjective
    (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) hdet x
  have hz : spectralTwoColumns (homogeneousDiagonal a b u) (homogeneousDiagonal a b v) z =
      homogeneousDiagonal a b (spectralTwoColumns u v z) := by
    rw [homogeneousDiagonal_columns, mul_apply_eq_comp]
  rw [sub_apply, spectralRobinOperator_columns _ _ _ _ z hdet, hz]
  change spectralTwoColumns (homogeneousDiagonal a b (K u + du))
      (homogeneousDiagonal a b (K v + dv)) z - K (homogeneousDiagonal a b (spectralTwoColumns u v z)) =
    homogeneousDiagonal a b (spectralTwoColumns du dv (spectralValueInverse u v
      (homogeneousDiagonal a⁻¹ b⁻¹ (homogeneousDiagonal a b (spectralTwoColumns u v z)))))
  rw [homogeneousDiagonal_inv_apply a b ha hb, spectralValueInverse_apply_columns u v z hd]
  have hcomm := congrArg (fun M : End => M (spectralTwoColumns u v z)) hK.eq
  simp only [mul_apply_eq_comp] at hcomm
  rw [hcomm]
  simp only [spectralTwoColumns_apply, map_add, map_smul, smul_add]
  abel

theorem homogeneousDiagonal_robin_bound (a b : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ‖a‖ = ρ) (hb : ‖b‖ = ρ) (u v du dv : V)
    (hd : spectralValueDet u v ≠ 0) (K : End)
    (hK : Commute K (homogeneousDiagonal a b)) :
    ‖spectralRobinOperator (homogeneousDiagonal a b u) (homogeneousDiagonal a b v)
        (homogeneousDiagonal a b (K u + du)) (homogeneousDiagonal a b (K v + dv)) - K‖ ≤
      (‖du‖ + ‖dv‖) * ‖spectralValueInverse u v‖ := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (ha.symm ▸ hρ)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hb.symm ▸ hρ)
  rw [homogeneousDiagonal_robin_difference a b ha0 hb0 u v du dv hd K hK]
  exact (homogeneousDiagonal_conjugate_norm a b ρ hρ ha hb _).trans
    ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (homogeneousTwoColumns_norm du dv) (norm_nonneg _)))

theorem homogeneousValueInverse_tendsto {α : Type*} {l : Filter α}
    (u v : α → V) (u₀ v₀ : V)
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀))
    (hd : spectralValueDet u₀ v₀ ≠ 0) :
    Tendsto (fun t => spectralValueInverse (u t) (v t)) l
      (𝓝 (spectralValueInverse u₀ v₀)) := by
  have hcol :=
    (((ContinuousLinearMap.smulRightL ℂ V V (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.continuousAt.tendsto).comp
      (hv.snd_nhds.prodMk_nhds hu.snd_nhds.neg)).add
    (((ContinuousLinearMap.smulRightL ℂ V V (ContinuousLinearMap.snd ℂ ℂ ℂ)).continuous.continuousAt.tendsto).comp
      (hv.fst_nhds.neg.prodMk_nhds hu.fst_nhds))
  have hdet := (hu.fst_nhds.mul hv.snd_nhds).sub (hu.snd_nhds.mul hv.fst_nhds)
  exact (hdet.inv₀ hd).smul hcol

theorem homogeneousNormalizedInverse_bound (u v : ℝ → V)
    (hu : Tendsto u atTop (𝓝 (1, 0))) (hv : Tendsto v atTop (𝓝 (0, 1))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in atTop,
      spectralValueDet (u t) (v t) ≠ 0 ∧ ‖spectralValueInverse (u t) (v t)‖ ≤ K := by
  have hd : spectralValueDet (1, 0) (0, 1) ≠ 0 := by norm_num [spectralValueDet]
  have hinv := homogeneousValueInverse_tendsto u v (1, 0) (0, 1) hu hv hd
  have hdet : Tendsto (fun t => spectralValueDet (u t) (v t)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [spectralValueDet, one_mul, zero_mul, sub_zero] using
      (hu.fst_nhds.mul hv.snd_nhds).sub (hu.snd_nhds.mul hv.fst_nhds)
  refine ⟨‖spectralValueInverse (1, 0) (0, 1)‖ + 1, by positivity, ?_⟩
  filter_upwards [hdet.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)),
    hinv.norm.eventually (gt_mem_nhds (show ‖spectralValueInverse (1, 0) (0, 1)‖ <
      ‖spectralValueInverse (1, 0) (0, 1)‖ + 1 by linarith))] with t ht hb
  exact ⟨ht, hb.le⟩

end DefocusingNLS

end OAI
