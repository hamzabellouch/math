import OAI.NumberTheory.JointDickman.Amplification.PrincipalBinRestriction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace OAI

/-! # A common centering constant for all fixed-modulus character averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem all_characters_weightedBinAverage_short
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hBill : FiniteBinDistributionInput)
    {J : ℕ} (hJ : 2 ≤ J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ χ : DirichletCharacter ℂ q,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
  obtain ⟨μ,hμ,hprincipal⟩ := principal_weightedBinAverage_short hMR hBill hJ ζ hζ
    P hP t ht (q := q) A scale H hA hscale hH
  refine ⟨μ,hμ,?_⟩
  intro ε hε
  have hχ (χ : DirichletCharacter ℂ q) : ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
    by_cases he : χ = 1
    · subst χ
      exact hprincipal ε hε
    · exact nonprincipal_weightedBinAverage_short hMRT hKMT hM J (by omega)
        (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ μ P hP t ht χ he
        A scale H hA hscale hH ε hε
  filter_upwards [eventually_all.mpr hχ] with B hb
  exact eventually_all.mpr hb

end JointDickman

end OAI
