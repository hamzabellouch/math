import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial

namespace OAI

/-! The finite endpoint cost when a divided outer cutoff exceeds the
range supported by the original distance hypothesis. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_short_outer_endpoint (B : ℕ → ℂ) (hB : OneBounded B)
    (Y Z D H : ℕ) (hYZ : Y ≤ Z+D) (α : ℝ) :
    shortExponentialIntegral B Y H α ≤
      shortExponentialIntegral B Z H α+(D:ℝ)*H := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ n ∈ range (Z+D), ‖shortExponentialSum B H α n‖ :=
      sum_le_sum_of_subset_of_nonneg (range_mono hYZ) (fun _ _ _ => norm_nonneg _)
    _ = (∑ n ∈ range Z, ‖shortExponentialSum B H α n‖)+
        ∑ n ∈ range D, ‖shortExponentialSum B H α ((Z+n : ℕ) : ℝ)‖ :=
      sum_range_add _ _ _
    _ ≤ (∑ n ∈ range Z, ‖shortExponentialSum B H α n‖)+
        ∑ _n ∈ range D, (H:ℝ) :=
      add_le_add le_rfl (sum_le_sum (fun n _ => minor_arc_short_sum_trivial B hB H (Z+n) α))
    _ = _ := by simp

end TwoPointCorrelations

end OAI
