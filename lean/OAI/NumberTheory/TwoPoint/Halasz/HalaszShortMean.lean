import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortL1

namespace OAI

/-! Convert the actual typical short-sum energy to the published L1
quantity while retaining the linear error from discarded integers. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_short_square_cells (F : ℕ → ℂ) (A N H : ℕ) (α : ℝ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖^2) =
      ∑ v ∈ range N, ‖shortExponentialSum F H α (A+v:ℕ)‖^2 := by
  have hi (v : ℕ) : IntervalIntegrable (fun x => ‖shortExponentialSum F H α x‖^2)
      volume (v:ℝ) (v+1) := by
    apply (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖shortExponentialSum F H α v‖^2) volume (v:ℝ) (v+1)).congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le (by linarith : (v:ℝ) ≤ v+1)] at hx
    dsimp only
    rw [shortExponentialSum_on_unit_cell F H α v ⟨hx.1.le, hx.2⟩]
  have he (v : ℕ) : (∫ x in (v:ℝ)..(v+1), ‖shortExponentialSum F H α x‖^2) =
      ‖shortExponentialSum F H α v‖^2 := by
    calc
      _ = ∫ _x in (v:ℝ)..(v+1), ‖shortExponentialSum F H α v‖^2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx
        dsimp only
        rw [shortExponentialSum_on_unit_cell F H α v ⟨hx.1.le, hx.2⟩]
      _ = _ := by simp
  symm
  calc
    _ = ∑ v ∈ range N, ∫ x in (A+v:ℕ)..(A+v+1:ℕ),
        ‖shortExponentialSum F H α x‖^2 := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using (he (A+v)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => ((A+n:ℕ):ℝ)) (n := N)
          (fun v _ => by simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using hi (A+v)))

lemma halasz_short_mean_square (F : ℕ → ℂ) {N H : ℕ}
    (hN : 0 < N) (hH : 0 < H) (α : ℝ) :
    ((∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H α x‖) / ((N:ℝ)*H))^2 ≤
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H α x‖^2) / ((N:ℝ)*(H:ℝ)^2) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hs := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1:ℝ))
    (fun v => ‖shortExponentialSum F H α (N+v:ℕ)‖)
  simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hs
  have he : (2*(N:ℝ)) = ((N+N:ℕ):ℝ) := by push_cast; ring
  rw [he, halasz_short_integral_cells, halasz_short_square_cells]
  calc
    _ = (∑ v ∈ range N, ‖shortExponentialSum F H α (N+v:ℕ)‖)^2 /
        ((N:ℝ)^2*(H:ℝ)^2) := by rw [div_pow, mul_pow]
    _ ≤ ((N:ℝ)*(∑ v ∈ range N, ‖shortExponentialSum F H α (N+v:ℕ)‖^2)) /
        ((N:ℝ)^2*(H:ℝ)^2) := div_le_div_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp

theorem halasz_short_mean_transfer {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {N H : ℕ} [NeZero (N+H)] (hH : 0 < H) (hHN : H ≤ N) {δ ε : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : (uniformFiniteLaw (Fin (N+H))).probability
      (fun n => ¬mrtTypical J P (N+1+n.val)) ≤ δ)
    (htyp : (∫ x in (N:ℝ)..(2*N),
        ‖shortExponentialSum (mrtTypicalCoefficient J P F) H 0 x‖^2) /
          ((N:ℝ)*(H:ℝ)^2) ≤ ε) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H 0 x‖) / ((N:ℝ)*H) ≤
      Real.sqrt ε + 2*δ := by
  have hN : 0 < N := hH.trans_le hHN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hm := Real.le_sqrt_of_sq_le
    ((halasz_short_mean_square (mrtTypicalCoefficient J P F) hN hH 0).trans htyp)
  have hl := halasz_typical_short_L1 J P F hF N N H 0 δ hδ
  have he : ((N+N:ℕ):ℝ) = 2*(N:ℝ) := by push_cast; ring
  rw [he] at hl
  have hd := div_le_div_of_nonneg_right hl (mul_nonneg hNr.le hHr.le)
  rw [add_div] at hd
  apply hd.trans
  apply add_le_add hm
  apply (div_le_iff₀ (mul_pos hNr hHr)).mpr
  have hHNr : (H:ℝ) ≤ N := by exact_mod_cast hHN
  nlinarith [mul_nonneg (mul_nonneg hHr.le hδ0) (sub_nonneg.mpr hHNr)]

end TwoPointCorrelations

end OAI
