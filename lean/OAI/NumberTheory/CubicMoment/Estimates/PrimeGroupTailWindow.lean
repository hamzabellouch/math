import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointRegularity
import OAI.NumberTheory.CubicMoment.Estimates.DyadicWeightIntegral
import OAI.NumberTheory.CubicMoment.Estimates.BilinearHeightTail

namespace OAI

/-! A literal Fourier cutoff window is controlled by the two-sided height
mean of the original Gauss polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma primeGroupTail_window_le_mean (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (H X T : ℝ) (hX : 0 < X) (hT : 0 < T) :
    ‖cutoffBilinearWindow P S α β H T X‖ ≤
      2*dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist t (a*b)‖) T := by
  let f := fun t => ∑ a ∈ P, ∑ b ∈ S,
    α a*β b*gauss (a*b)*normTwist t (a*b)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul (continuous_normTwist (a*b))
  have hv (Y : ℝ) : ‖heightBilinearValue P S α β (localizedEndpointWeight H T) Y T‖ ≤
      dyadicHeightMean (fun t => ‖f t‖) T := by
    rw [heightBilinearValue_eq_integral P S α β _ (localizedEndpointWeight_integrable H hT)]
    have hb := normalized_dyadicWeightIntegral_bound f
      (fun t => localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))
      hf hT (show (0:ℝ) ≤ 1 by norm_num) (fun t => by
        rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
        exact localizedEndpointWeight_norm_le H hT t)
      (fun t ht => by rw [localizedEndpointWeight_zero H hT t ht,zero_mul])
    simpa only [one_mul] using hb
  unfold cutoffBilinearWindow
  rw [bilinear_cutoff_window_endpoints P S α β H hT hX]
  exact (norm_sub_le _ _).trans ((add_le_add (hv X) (hv (2*X))).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
