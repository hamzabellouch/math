import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins
import OAI.MeasureTheory.Falconer.Recursion.Ledger

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem coincidence_le_bin_sq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≤ d.normalization * (((bandOffsets 100).card : ℝ≥0∞)*
      (binL2Norm d.distance d.width)^2) := by
  have hh := real_bin_shifted_band_bound d.distance d.distance d.width_pos 100 0
  simp only [sub_zero,← pow_two] at hh
  rw [d.distance_collision] at hh
  exact mul_le_mul' le_rfl hh

theorem suffix_normalization_ratio (d : PositiveDistanceData) (p : ℕ) :
    d.normalization * ({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ =
      ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p)) := by
  rw [normalization_inv]
  change ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)/d.levelMass^4) *
    ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((p:ℝ)-d.a))) = _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hm : d.levelMass^4 ≠ 0 := pow_ne_zero _ d.levelMass_pos.ne'
  calc
    _ = (2:ℝ)^((d.t:ℝ)-d.a)*(2:ℝ)^(-((p:ℝ)-d.a)) := by field_simp [d.levelMass_pos.ne']
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring

theorem suffix_normalized_from_bins (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (p : ℕ) (F : ℝ≥0∞)
    (hbin : (binL2Norm d.distance d.width)^2 ≤
      F*({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ *
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence) :
    d.coincidence ≤ ((bandOffsets 100).card : ℝ≥0∞)*F*
      ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p))*
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  have hh := d.coincidence_le_bin_sq.trans
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hbin))
  apply hh.trans_eq
  calc
    _ = ((bandOffsets 100).card : ℝ≥0∞)*F*
        (d.normalization*({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹)*
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by ring
    _ = _ := by rw [d.suffix_normalization_ratio]

end PositiveDistanceData

theorem suffix_profile_power_identity (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (p t : ℕ) (loss : ℝ) :
    ((2:ℝ)^N)^(-(m t-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p t+loss)*
      (2:ℝ)^((t:ℝ)-p) =
      ((2:ℝ)^N)^((m p-(p:ℝ)/(N:ℝ))-intervalMin (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p t+loss) := by
  have hnr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hscale : (2:ℝ)^((t:ℝ)-p) = ((2:ℝ)^N)^(((t:ℝ)-p)/(N:ℝ)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  rw [hscale,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  congr 1
  unfold height
  ring

end PlanarFalconer

end OAI
