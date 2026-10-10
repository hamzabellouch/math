import OAI.Geometry.CylinderCovering.Footprints.Footprints

namespace OAI

open Filter MeasureTheory
open scoped Topology

namespace CylinderCovering.Footprints

theorem sum_quadratic_mesh_error_tendsto_zero {L K : ℝ}
    (E : (n : ℕ) → Fin n → ℝ)
    (hE : ∀ n : ℕ, L / (n : ℝ) ≤ 1 → ∀ i,
      0 ≤ E n i ∧ E n i ≤ K * (L / (n : ℝ)) ^ 2) :
    Tendsto (fun n => ∑ i, E n i) atTop (𝓝 0) := by
  have hdlim : Tendsto (fun n : ℕ => L / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds.mul (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0)))
  have hd1 : ∀ᶠ n : ℕ in atTop, L / (n : ℝ) ≤ 1 :=
    ((tendsto_order.1 hdlim).2 1 (by norm_num)).mono (fun n hn => le_of_lt hn)
  have hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ (∑ i, E n i) ∧ (∑ i, E n i) ≤ (K * L) * (L / (n : ℝ)) := by
    filter_upwards [hd1, eventually_gt_atTop 0] with n hn hn0
    refine ⟨Finset.sum_nonneg (fun i hi => (hE n hn i).1), ?_⟩
    calc
      (∑ i, E n i) ≤ ∑ _i : Fin n, K * (L / (n : ℝ)) ^ 2 := by
        exact Finset.sum_le_sum (fun i hi => (hE n hn i).2)
      _ = (K * L) * (L / (n : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
        field_simp
  apply squeeze_zero' (hbound.mono (fun n hn => hn.1)) (hbound.mono (fun n hn => hn.2))
  simpa only [mul_zero] using tendsto_const_nhds.mul hdlim

theorem absolute_sum_error_tendsto_zero {L R A B h : ℝ}
    (M W : (n : ℕ) → Fin n → ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hM : ∀ n i, 0 ≤ M n i) (hMR : ∀ n i, M n i ≤ R)
    (hW : ∀ n i, 0 ≤ W n i) (hWh : ∀ n i, W n i ≤ h) :
    Tendsto (fun n =>
      (∑ i, W n i * absoluteArea (M n i) (L / (n : ℝ)) A B) -
      (∑ i, W n i * ((L / (n : ℝ)) * (M n i) ^ 2 / 2))) atTop (𝓝 0) := by
  let E := fun (n : ℕ) (i : Fin n) => W n i *
    (absoluteArea (M n i) (L / (n : ℝ)) A B - (L / (n : ℝ)) * (M n i) ^ 2 / 2)
  have he : ∀ n : ℕ, L / (n : ℝ) ≤ 1 → ∀ i, 0 ≤ E n i ∧
      E n i ≤ (h * ((A + 2 * B) * R + (A ^ 2 + 4 * A * B))) * (L / (n : ℝ)) ^ 2 := by
    intro n hn i
    have hd : 0 ≤ L / (n : ℝ) := div_nonneg hL (Nat.cast_nonneg n)
    have hb := absoluteArea_error_bound (hM n i) (hMR n i) hd hn hA hB
    refine ⟨mul_nonneg (hW n i) hb.1, ?_⟩
    have hp := mul_le_mul (hWh n i) hb.2 hb.1 hh
    dsimp [E]
    nlinarith only [hp]
  have ht := sum_quadratic_mesh_error_tendsto_zero E he
  convert ht using 1
  ext n
  simp only [E, mul_sub, Finset.sum_sub_distrib]

theorem affine_sum_error_tendsto_zero {L R A B h : ℝ}
    (M W : (n : ℕ) → Fin n → ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hM : ∀ n i, 0 ≤ M n i) (hMR : ∀ n i, M n i ≤ R)
    (hW : ∀ n i, 0 ≤ W n i) (hWh : ∀ n i, W n i ≤ h) :
    Tendsto (fun n =>
      (∑ i, W n i * affineArea (M n i) (L / (n : ℝ)) A B) -
      (∑ i, W n i * ((L / (n : ℝ)) * (M n i) ^ 2 / 2))) atTop (𝓝 0) := by
  let E := fun (n : ℕ) (i : Fin n) => W n i *
    (affineArea (M n i) (L / (n : ℝ)) A B - (L / (n : ℝ)) * (M n i) ^ 2 / 2)
  have he : ∀ n : ℕ, L / (n : ℝ) ≤ 1 → ∀ i, 0 ≤ E n i ∧
      E n i ≤ (h * ((A + 2 * B) * R + 4 * A * B)) * (L / (n : ℝ)) ^ 2 := by
    intro n hn i
    have hd : 0 ≤ L / (n : ℝ) := div_nonneg hL (Nat.cast_nonneg n)
    have hb := affineArea_error_bound (hM n i) (hMR n i) hd hn hA hB
    refine ⟨mul_nonneg (hW n i) hb.1, ?_⟩
    have hp := mul_le_mul (hWh n i) hb.2 hb.1 hh
    dsimp [E]
    nlinarith only [hp]
  have ht := sum_quadratic_mesh_error_tendsto_zero E he
  convert ht using 1
  ext n
  simp only [E, mul_sub, Finset.sum_sub_distrib]

theorem absolute_volume_sum_error_tendsto_zero {L R A B h : ℝ}
    (M W S : (n : ℕ) → Fin n → ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hM : ∀ n i, 0 ≤ M n i) (hMR : ∀ n i, M n i ≤ R)
    (hW : ∀ n i, 0 ≤ W n i) (hWh : ∀ n i, W n i ≤ h) :
    Tendsto (fun n =>
      (∑ i, W n i * volume.real (absoluteFootprint (S n i) (M n i) (L / (n : ℝ)) A B)) -
      (∑ i, W n i * ((L / (n : ℝ)) * (M n i) ^ 2 / 2))) atTop (𝓝 0) := by
  have ht := absolute_sum_error_tendsto_zero M W hL hA hB hh hM hMR hW hWh
  convert ht using 1
  ext n
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [realVolume_absoluteFootprint (hM n i) (div_nonneg hL (Nat.cast_nonneg n)) hA hB]

theorem affine_volume_sum_error_tendsto_zero {L R A B h : ℝ}
    (M W S : (n : ℕ) → Fin n → ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hAB : A / 2 ≤ B) (hh : 0 ≤ h)
    (hM : ∀ n i, 0 ≤ M n i) (hMR : ∀ n i, M n i ≤ R)
    (hW : ∀ n i, 0 ≤ W n i) (hWh : ∀ n i, W n i ≤ h) :
    Tendsto (fun n =>
      (∑ i, W n i * volume.real (affineFootprint (S n i) (M n i) (L / (n : ℝ)) A B)) -
      (∑ i, W n i * ((L / (n : ℝ)) * (M n i) ^ 2 / 2))) atTop (𝓝 0) := by
  have hB : 0 ≤ B := by linarith
  have ht := affine_sum_error_tendsto_zero M W hL hA hB hh hM hMR hW hWh
  convert ht using 1
  ext n
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [realVolume_affineFootprint (hM n i) (div_nonneg hL (Nat.cast_nonneg n)) hA hAB]

end CylinderCovering.Footprints

end OAI
