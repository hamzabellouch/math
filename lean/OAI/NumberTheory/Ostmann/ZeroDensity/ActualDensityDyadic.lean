import OAI.NumberTheory.Ostmann.ZeroDensity.OccurrenceCount
import OAI.NumberTheory.Ostmann.ZeroDensity.SelectedDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.SeparatedSelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem exists_actual_zero_density_dyadic_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q)) (σ : ℝ),
      0 < Q → 0 < H → 1/2 ≤ σ → σ ≤ 1 →
      (totalZeroCount Q exception σ (H : ℝ) : ℝ) ≤
        8*C*localMultiplicityBound Q H*
          (detectorBlockCount (detectorLength Q H (Q^2*H)) : ℝ) *
          ∑ j ∈ Finset.range (detectorBlockCount (detectorLength Q H (Q^2*H))),
            (((2^j*(Q^2*H) : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
              (1+Real.log (2*(2^j*(Q^2*H) : ℕ) : ℝ))^7 *
                (2^j*(Q^2*H) : ℕ) * ((2^j*(Q^2*H) : ℕ) : ℝ)^(-2*σ) := by
  classical
  obtain ⟨C,hC,hselected⟩ := exists_selected_zero_density_constant
  refine ⟨C,hC,?_⟩
  intro Q H exception σ hQ hH hσ hσ1
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨r,hrs,hsep,hcard⟩ := exists_separated_selection
    (retainedZeros Q exception σ (H : ℝ))
    (fun z => z.1) (fun z => z.point.im)
    (retainedZeros_local_card_le Q exception hσ hHR)
  have hr := hselected Q H exception σ r hQ hH hσ hσ1 hrs hsep
  have hB := localMultiplicityBound_nonneg hQ hHR
  calc
    (totalZeroCount Q exception σ (H : ℝ) : ℝ) ≤
        2*localMultiplicityBound Q H*r.card := hcard
    _ ≤ 2*localMultiplicityBound Q H*
        (4*C*(detectorBlockCount (detectorLength Q H (Q^2*H)) : ℝ) *
          ∑ j ∈ Finset.range (detectorBlockCount (detectorLength Q H (Q^2*H))),
            (((2^j*(Q^2*H) : ℕ) : ℝ)+(Q : ℝ)^2*H) * (1+Real.log Q) *
              (1+Real.log (2*(2^j*(Q^2*H) : ℕ) : ℝ))^7 *
                (2^j*(Q^2*H) : ℕ) * ((2^j*(Q^2*H) : ℕ) : ℝ)^(-2*σ)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

end Ostmann.ZeroDensity

end

end OAI
