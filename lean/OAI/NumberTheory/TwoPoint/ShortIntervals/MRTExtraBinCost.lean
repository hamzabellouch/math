import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBandGeometry

namespace OAI

/-! The full extra-bin multiplicity fits the cofactor saving. A crude
Cauchy sum suffices; no loss involving the number of original bands occurs. -/

namespace TwoPointCorrelations

open Finset

lemma mrt_extra_bin_card {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤
      2*mrtExtraPrimeResolution L*L/Real.log L := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log L := by linarith
  have hH : 1 ≤ mrtExtraPrimeResolution L := Real.one_le_rpow hL (by norm_num)
  have hq : 1 ≤ L/Real.log L := (le_div_iff₀ hlog0).mpr (by
    linarith [Real.log_le_sub_one_of_pos hL0])
  have hQ : 1 ≤ mrtExtraPrimeUpper L := Real.one_le_exp (by positivity)
  have hh := mrt_log_bin_card (P := mrtExtraPrimeLower L) (by linarith :
    0 ≤ mrtExtraPrimeResolution L) hQ
  have hprod := one_le_mul_of_one_le_of_one_le hH hq
  calc
    _ ≤ mrtExtraPrimeResolution L*Real.log (mrtExtraPrimeUpper L)+1 := hh
    _ = mrtExtraPrimeResolution L*(L/Real.log L)+1 := by
      rw [mrtExtraPrimeUpper,Real.log_exp]
    _ ≤ 2*(mrtExtraPrimeResolution L*(L/Real.log L)) := by linarith
    _ = _ := by ring

theorem mrt_extra_bin_cofactor_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ)^2) /
      (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2) ≤ 4*L^(3/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < mrtExtraPrimeResolution L := Real.rpow_pos_of_pos hL0 _
  have hcard := mrt_extra_bin_card hL hlog
  have hratio : L/Real.log L ≤ L := div_le_self hL0.le hlog
  have hc : ((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
      (mrtExtraPrimeUpper L)).card:ℝ) ≤ 2*mrtExtraPrimeResolution L*L := by
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*mrtExtraPrimeResolution L by positivity)
    exact hcard.trans (by simpa only [mul_div_assoc] using hh)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hp : (L^(79/80:ℝ))^2=L^(79/40:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  have he : (2*mrtExtraPrimeResolution L*L)^2 /
      (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2) = 4*L^(3/80:ℝ) := by
    calc
      _ = 4*(mrtExtraPrimeResolution L*L^2)/(L^(79/80:ℝ))^2 := by
        field_simp [hH0.ne']
        ring
      _ = 4*(L^(1/80:ℝ)*L^(2:ℝ))/L^(79/40:ℝ) := by
        rw [hp,Real.rpow_two]
        rfl
      _ = 4*L^(161/80:ℝ)/L^(79/40:ℝ) := by
        rw [← Real.rpow_add hL0]
        norm_num
      _ = _ := by
        rw [mul_div_assoc,← Real.rpow_sub hL0]
        norm_num
  exact (div_le_div_of_nonneg_right hsq (by positivity)).trans_eq he

/-- The retained cofactor exponent 1/40 pays all extra-bin factors. -/
theorem mrt_extra_bin_saved_cost {L : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) :
    (L^(-1/40:ℝ))^2 *
      ((((mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L)).card:ℝ)^2) /
        (mrtExtraPrimeResolution L*(L^(79/80:ℝ))^2)) ≤ 4*L^(-1/80:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hh := mul_le_mul_of_nonneg_left (mrt_extra_bin_cofactor_cost hL hlog)
    (sq_nonneg (L^(-1/40:ℝ)))
  apply hh.trans_eq
  have he : (L^(-1/40:ℝ))^2=L^(-1/20:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  rw [he]
  calc
    _ = 4*(L^(-1/20:ℝ)*L^(3/80:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

end TwoPointCorrelations

end OAI
