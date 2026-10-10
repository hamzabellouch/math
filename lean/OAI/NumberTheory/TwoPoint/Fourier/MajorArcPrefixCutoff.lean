import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbedSharp
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial

namespace OAI

/-! Very short prefixes use boundedness; character estimates are only
needed above the cutoff where all divided windows remain long. -/
namespace TwoPointCorrelations

lemma major_arc_prefix_cutoff (B : ℕ → ℂ) (hB : OneBounded B)
    (X H : ℕ) (α U K : ℝ) (hsmall : (X:ℝ)*U ≤ K)
    (hlong : ∀ h : ℕ, 1 ≤ h → h ≤ H → U ≤ (h:ℝ) →
      shortExponentialIntegral B X h α ≤ K) :
    ∀ h : ℕ, 1 ≤ h → h ≤ H → shortExponentialIntegral B X h α ≤ K := by
  intro h hh hhH
  by_cases hu : U ≤ (h:ℝ)
  · exact hlong h hh hhH hu
  · exact (minor_arc_short_integral_trivial B hB X h α).trans
      ((mul_le_mul_of_nonneg_left (le_of_not_ge hu) (Nat.cast_nonneg X)).trans hsmall)

theorem major_arc_perturbation_cutoff (B : ℕ → ℂ) (hB : OneBounded B)
    (X H : ℕ) (hH : 0 < H) (α β U K : ℝ) (hK : 0 ≤ K)
    (hsmall : (X:ℝ)*U ≤ K) (hphase : |β| *(H:ℝ) ≤ 1)
    (hlong : ∀ h : ℕ, 1 ≤ h → h ≤ H → U ≤ (h:ℝ) →
      shortExponentialIntegral B X h α ≤ K) :
    shortExponentialIntegral B X H (α+β) ≤ (1+2*Real.pi)*K := by
  apply (major_arc_integral_perturbation_uniform B X H hH α β K hK
    (major_arc_prefix_cutoff B hB X H α U K hsmall hlong)).trans
  apply mul_le_mul_of_nonneg_right _ hK
  nlinarith [Real.pi_pos]

theorem major_arc_perturbation_cutoff_two (B : ℕ → ℂ) (hB : OneBounded B)
    (X H : ℕ) (hH : 0 < H) (α β U K : ℝ) (hK : 0 ≤ K)
    (hsmall : (X:ℝ)*U ≤ K) (hphase : |β| *(H:ℝ) ≤ 2)
    (hlong : ∀ h : ℕ, 1 ≤ h → h ≤ H → U ≤ (h:ℝ) →
      shortExponentialIntegral B X h α ≤ K) :
    shortExponentialIntegral B X H (α+β) ≤ (1+4*Real.pi)*K := by
  apply (major_arc_integral_perturbation_uniform B X H hH α β K hK
    (major_arc_prefix_cutoff B hB X H α U K hsmall hlong)).trans
  apply mul_le_mul_of_nonneg_right _ hK
  nlinarith [Real.pi_pos]

end TwoPointCorrelations

end OAI
