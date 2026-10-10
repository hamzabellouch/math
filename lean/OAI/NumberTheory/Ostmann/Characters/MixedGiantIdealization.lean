import OAI.NumberTheory.Ostmann.Construction.IntegerCellPriors
import OAI.NumberTheory.Ostmann.Construction.PrimeCellIdealization
import OAI.NumberTheory.Ostmann.Construction.FinitePairCells

namespace OAI

/-! # Joint idealization of the external integer and prime giants

Only the prime coordinate uses a published input. Both error terms below
are derived from their original sampling laws, and the Page correction
remains inside the prime ideal measure.
-/

namespace Ostmann

open scoped BigOperators Classical
open MeasureTheory

theorem PublishedProgressionInput.mixed_giant_idealization
    (P : PublishedProgressionInput) (Q : ℕ) (hQ : 2 ≤ Q)
    (SI SP : Finset ℕ) {C D : Type*} [Fintype C] [Fintype D]
    (DI : IntegerCellPartition SI C) (DP : PrimeCellPartition SP D)
    (hmod : DP.modulus ≤ Q) (wI wP : ℝ → ℝ) (G ZI ZP : ℝ)
    (hZI : 0 ≤ ZI) (hZP : 0 ≤ ZP)
    (hwI : ∀ n ∈ SI, 0 ≤ wI (Real.log n))
    (hwP : ∀ p ∈ SP, 0 ≤ wP (Real.log p))
    (hwiI : ∀ c y, y ∈ Set.Ioc (DI.lower c) (DI.upper c) → 0 ≤ wI y)
    (hmassI : ZI * Real.exp (-G) * (∑ n ∈ SI, wI (Real.log n)) ≤ 1)
    (hmassP : ZP * (∑ p ∈ SP, wP (Real.log p) * (p : ℝ)⁻¹) ≤ 1)
    (hwcI : ∀ c, ContinuousOn wI (Set.Icc (DI.lower c) (DI.upper c)))
    (hwcP : ∀ d, ContinuousOn wP (Set.Icc (DP.lower d) (DP.upper d)))
    (wI₀ : C → ℝ) (wP₀ : D → ℝ) (ηI ηP δI δP K η : ℝ)
    (hηI : 0 ≤ ηI) (hηP : 0 ≤ ηP) (hδI : 0 ≤ δI) (hδP : 0 ≤ δP)
    (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hvarI : ∀ c y, y ∈ Set.Ioc (DI.lower c) (DI.upper c) → |wI y - wI₀ c| ≤ ηI)
    (hvarP : ∀ d y, y ∈ Set.Ioc (DP.lower d) (DP.upper d) → |wP y - wP₀ d| ≤ ηP)
    (hbudgetI : ∀ c, ZI * ((|wI₀ c| + ηI) * (2 * Real.exp (-G)) +
      2 * ηI * Real.exp (DI.upper c - G)) ≤ δI)
    (hbudgetP : ∀ d, ZP * ((|wP₀ d| + ηP) *
      (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (DP.lower d)) +
        Real.exp (-P.kappa * DP.lower d / Real.log (4 * (Q : ℝ)))) + 4 * ηP) ≤ δP)
    (hsmallI : Fintype.card C * δI ≤ 1)
    (H : SI × SP → ℂ) (F : C × D → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ K)
    (hfreeze : ∀ x, ‖H x - F (DI.cell x.1, DP.cell x.2)‖ ≤ η) :
    ‖(∑ x : SI × SP,
        ((integerSamplePrior SI wI G ZI x.1 * primeSamplePrior SP wP ZP x.2 : ℝ) : ℂ) * H x) -
      ∑ y : C × D,
        ((idealIntegerCellPrior DI wI G ZI y.1 * idealPrimeCellPrior P Q DP wP ZP y.2 : ℝ) : ℂ) * F y‖ ≤
      η + K * (Fintype.card C * δI + 2 * (Fintype.card D * δP)) := by
  apply finite_pair_cell_idealization
    (integerSamplePrior SI wI G ZI) (primeSamplePrior SP wP ZP)
    (fun n => DI.cell n) (fun p => DP.cell p)
    (idealIntegerCellPrior DI wI G ZI) (idealPrimeCellPrior P Q DP wP ZP)
    (integerSamplePrior_nonneg SI wI G ZI hZI hwI)
    (primeSamplePrior_nonneg SP wP ZP hZP hwP)
    (idealIntegerCellPrior_nonneg DI wI G ZI hZI hwiI)
    (by rw [integerSamplePrior_mass]; exact hmassI)
    (by rw [primeSamplePrior_mass]; exact hmassP)
    δI δP K η hδI hδP hK hη hsmallI _ _ H F hF hfreeze
  · intro c
    exact (integerSamplePrior_cell_error DI wI G ZI hZI c (hwcI c)
      (wI₀ c) ηI hηI (hvarI c)).trans (hbudgetI c)
  · intro d
    exact (P.primeSamplePrior_cell_error SP wP ZP hZP DP.cell d
      hQ DP.modulus_pos hmod (DP.coprime d) (DP.lower_one d) (DP.ordered d)
      (DP.short d) (DP.fiber d) (hwcP d) (wP₀ d) ηP hηP (hvarP d)).trans (hbudgetP d)

end Ostmann

end OAI
