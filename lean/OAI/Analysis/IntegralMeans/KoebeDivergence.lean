import OAI.Analysis.IntegralMeans.AffineArea
import OAI.Analysis.IntegralMeans.KoebePolar
import OAI.Analysis.IntegralMeans.SectorDivergence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_negative_endpoint_area : areaMoment koebeMap disk (-2) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ))) (-1 + w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_left_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_left_lower hr hθ))
  rw [lintegral_left_disk_indicator] at h
  exact h

lemma koebe_positive_endpoint_area : areaMoment koebeMap disk (2 / 3) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ))) (1 - w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_right_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_right_lower hr hθ))
  rw [lintegral_right_disk_indicator] at h
  exact h

end Brennan.Sharp

end

end OAI
