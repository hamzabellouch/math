import OAI.Probability.InvariantIsing.Haar.HaarLipschitzTail

namespace OAI

/-! Both one-sided tails and the centered absolute deviation. -/
noncomputable section
open Matrix MeasureTheory Set
namespace InvariantIsing

theorem haar_lipschitz_lower_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ (∫ V, f V ∂μ)-f U} ≤
      Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have hh := haar_lipschitz_upper_tail hN μ (fun U => -f U) L hL
    (fun U V => by simpa only [neg_sub_neg,abs_sub_comm] using hLip U V) hr
  simpa only [integral_neg,sub_neg_eq_add,neg_add_eq_sub] using hh

theorem haar_lipschitz_mean_tail {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {r : ℝ} (hr : 0 < r) :
    μ.real {U | r ≤ |f U-(∫ V, f V ∂μ)|} ≤
      2*Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
  have he : {U | r ≤ |f U-(∫ V, f V ∂μ)|} =
      {U | r ≤ f U-(∫ V, f V ∂μ)} ∪ {U | r ≤ (∫ V, f V ∂μ)-f U} := by
    ext U
    simp only [mem_ofPred_eq,mem_union,le_abs,neg_sub]
  rw [he]
  calc
    _ ≤ μ.real {U | r ≤ f U-(∫ V, f V ∂μ)}+
        μ.real {U | r ≤ (∫ V, f V ∂μ)-f U} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-((N:ℝ)-2)*r^2/(8*L^2)) := by
      linarith [haar_lipschitz_upper_tail hN μ f L hL hLip hr,
        haar_lipschitz_lower_tail hN μ f L hL hLip hr]

end InvariantIsing

end

end OAI
