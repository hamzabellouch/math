import OAI.Analysis.IntegralMeans.Main
import OAI.Analysis.IntegralMeans.InverseMoment
import OAI.Analysis.IntegralMeans.KoebeDivergence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebe_inverse_four_area : areaMoment koebeInverse koebeDomain 4 = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_negative_endpoint_area

lemma koebe_inverse_four_thirds_area :
    areaMoment koebeInverse koebeDomain (4 / 3) = ⊤ := by
  rw [koebe_inverse_areaMoment]
  norm_num
  exact koebe_positive_endpoint_area

theorem sharp_endpoints : SharpEndpointStatement := by
  refine ⟨koebeMap_schlicht, koebe_negative_endpoint_area,
    koebe_positive_endpoint_area, ?_, ?_⟩
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_area
  · exact not_integrable_of_areaMoment_top koebe_inverse_four_thirds_area

end Brennan.Sharp

end

end OAI
