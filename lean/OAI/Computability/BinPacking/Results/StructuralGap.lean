import Mathlib.Algebra.Order.Floor.Semiring
import OAI.Computability.BinPacking.Configurations.K4Soundness
import OAI.Computability.BinPacking.Configurations.ReductionFractional

namespace OAI

namespace BinPackingGap

theorem completeFourGraph_reduction_bothLP_eq (c : ℕ) :
    individualLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) ∧
      typeLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) :=
  reduction_bothLP_eq c (1 / 8) completeFourGraph 2 (by decide)

theorem structural_additive_gap (c : ℕ) :
    ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  refine ⟨reductionInstance c (1 / 8) completeFourGraph 2,
    reductionBinBound c (1 / 8) completeFourGraph 2,
    reductionInstance_count c (1 / 8) completeFourGraph 2 (by decide),
    reductionInstance_size_bounds c (1 / 8) completeFourGraph 2,
    completeFourGraph_reduction_opt_gap c, ?_⟩
  exact completeFourGraph_reduction_bothLP_eq c

theorem exists_mirup_counterexample :
    ∃ I : Instance,
      Nat.ceil (individualLP I) + 1 < opt I ∧
        Nat.ceil (typeLP I) + 1 < opt I := by
  obtain ⟨I, B, _, _, hgap, hindividual, htype⟩ := structural_additive_gap 1
  refine ⟨I, ?_, ?_⟩
  · simpa only [hindividual, Nat.ceil_natCast] using hgap
  · simpa only [htype, Nat.ceil_natCast] using hgap

theorem individual_mirup_false :
    ¬ ∀ I : Instance, opt I ≤ Nat.ceil (individualLP I) + 1 := by
  intro h
  obtain ⟨I, hi, _⟩ := exists_mirup_counterexample
  exact (not_le_of_gt hi) (h I)

theorem type_mirup_false :
    ¬ ∀ I : Instance, opt I ≤ Nat.ceil (typeLP I) + 1 := by
  intro h
  obtain ⟨I, _, hi⟩ := exists_mirup_counterexample
  exact (not_le_of_gt hi) (h I)

end BinPackingGap

end OAI
