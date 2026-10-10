import OAI.Analysis.Pureness.Traces.TraceTransfer
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace OAI
namespace CuntzPureness
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem normalize_fullness_sum (I : Finset ι) (h : A) (hh : 0 ≤ h) (t : ι → A)
    (hunit : IsUnit (∑ i ∈ I, star (t i) * h * t i)) :
    ∃ s : ι → A, ∑ i ∈ I, star (s i) * h * s i = 1 := by
  let q := ∑ i ∈ I, star (t i) * h * t i
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => star_left_conjugate_nonneg hh (t i))
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff q hq).mpr hunit
  have hfactor : q = star (u : A) * (u : A) := by
    rw [hu, (CFC.sqrt_nonneg q).star_eq, CFC.sqrt_mul_sqrt_self q hq]
  have hnormalize : star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) = 1 := by
    rw [hfactor]
    calc
      star (↑(u⁻¹) : A) * (star (u : A) * (u : A)) * (↑(u⁻¹) : A) =
          star ((u : A) * (↑(u⁻¹) : A)) * ((u : A) * (↑(u⁻¹) : A)) := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by simp
  refine ⟨fun i => t i * (↑(u⁻¹) : A), ?_⟩
  calc
    (∑ i ∈ I, star (t i * (↑(u⁻¹) : A)) * h * (t i * (↑(u⁻¹) : A))) =
        star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) := by
      simp only [q, Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    _ = 1 := hnormalize

theorem sqrt_trace_transfer (I : Finset ι) (h p : A) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (s : ι → A) (hfull : ∑ i ∈ I, star (s i) * h * s i = 1) :
    0 ≤ traceTransfer I (CFC.sqrt h) p s ∧
      ∀ (τ : A →+ ℂ), (∀ a b : A, τ (a * b) = τ (b * a)) →
        τ (traceTransfer I (CFC.sqrt h) p s) = τ p := by
  constructor
  · exact traceTransfer_nonneg I _ p s (CFC.sqrt_nonneg h).star_eq hp
  · intro τ hτ
    apply trace_transfer_identity τ hτ I _ p s
    simpa only [CFC.sqrt_mul_sqrt_self h hh] using hfull
end CuntzPureness

end OAI
