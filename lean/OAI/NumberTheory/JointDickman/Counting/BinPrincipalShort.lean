import OAI.NumberTheory.JointDickman.Amplification.BinWeightedMarginal

namespace OAI

/-! # The principal short-average consequence from published inputs -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

theorem finitePrimeWeight_short_averages
    (hMR : RealShortIntervalInput) (hBill : FiniteBinDistributionInput)
    {J : ℕ} (hJ : 2 ≤ J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖weightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1))
          ζ μ (finitePrimeWeight (P B) (t B)) (H B) z‖^2) < ε := by
  obtain ⟨μ,hμ,hmean⟩ := centeredBinPrefix_of_published hBill hJ ζ hζ
  refine ⟨μ,hμ,?_⟩
  apply weightedBinAverage_eventually_eventually hMR J (by omega)
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ μ
    (fun B => finitePrimeWeight (P B) (t B))
    (fun B => finitePrimeWeight_multiplicative (hP B) (t B))
    (fun B n => by
      rw [abs_of_nonneg (finitePrimeWeight_bounds (ht B) n).1]
      exact (finitePrimeWeight_bounds (ht B) n).2)
    A hA scale hscale H hH
  intro B
  exact (weightedBinAverage_long_tendsto (by omega) ζ μ hmean (hP B) (t B) (hA B)).comp hscale

end JointDickman

end OAI
