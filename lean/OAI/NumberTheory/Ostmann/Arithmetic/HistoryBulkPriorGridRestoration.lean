import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridTuple

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement LogCellPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bulkFullMassRatio (L : ℝ) (E : Finset ℕ) : ℝ :=
  ∑ p ∈ bulkClosedSupport L, bulkWeight L E p

theorem bulkFullMassRatio_bounds (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < bulkNormalizer L E) :
    1 ≤ bulkFullMassRatio L E ∧ bulkFullMassRatio L E ≤ 1+bulkRestorationCap L E := by
  have h := bulkWeight_restoration_bound L E hZ
  change 0 ≤ bulkFullMassRatio L E-1 ∧ bulkFullMassRatio L E-1 ≤ bulkRestorationCap L E at h
  constructor <;> linarith [h.1,h.2]

omit [DecidableEq ι] in
theorem bulkTupleWeight_nonneg (L : ℝ) (E : Finset ℕ) (p : BulkPrimeTuple ι L) :
    0 ≤ bulkTupleWeight L E p :=
  Finset.prod_nonneg (fun i _ => bulkWeight_nonneg L E (p i).val)

theorem bulkTupleWeight_sum (L : ℝ) (E : Finset ℕ) :
    (∑ p : BulkPrimeTuple ι L, bulkTupleWeight L E p) =
      bulkFullMassRatio L E ^ Fintype.card ι := by
  have hs : (∑ p : {p : ℕ // p ∈ bulkClosedSupport L}, bulkWeight L E p.val) =
      bulkFullMassRatio L E := Finset.sum_coe_sort _ _
  calc
    _ = ∏ _i : ι, ∑ p : {p : ℕ // p ∈ bulkClosedSupport L}, bulkWeight L E p.val := by
      exact (Fintype.prod_sum (fun (_ : ι) (p : {p : ℕ // p ∈ bulkClosedSupport L}) =>
        bulkWeight L E p.val)).symm
    _ = _ := by simp only [hs, Finset.prod_const, Finset.card_univ]

theorem bulkTupleWeight_retained_sum (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) :
    (∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then bulkTupleWeight L E p else 0) = 1 := by
  have he := bulkProductPrior_cmean_eq_retained_grid (ι := ι) L E hZ (fun _ => 1)
  have hc : (bulkProductPrior (ι := ι) L E hZ).cmean (fun _ => (1 : ℂ)) = 1 := by
    simp only [FinitePrior.cmean, mul_one, ← Complex.ofReal_sum, FinitePrior.mass_total,
      Complex.ofReal_one]
  rw [hc] at he
  have hh := congrArg Complex.re he.symm
  simpa [apply_ite] using hh

theorem bulkTupleWeight_discarded_sum (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) :
    (∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then 0 else bulkTupleWeight L E p) =
      bulkFullMassRatio L E ^ Fintype.card ι-1 := by
  have hs : (∑ p : BulkPrimeTuple ι L, bulkTupleWeight L E p) =
      (∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then bulkTupleWeight L E p else 0) +
      (∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then 0 else bulkTupleWeight L E p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp
  rw [bulkTupleWeight_sum, bulkTupleWeight_retained_sum L E hZ] at hs
  linarith

theorem bulkGridMean_sub_source_cmean_le (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℂ)
    {A : ℝ} (_hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple ι L, ‖F (fun i => (p i).val)‖ ≤ A) :
    ‖bulkGridMean L E F-
      (bulkProductPrior (ι := ι) L E hZ).cmean (fun p => F (fun i => (p i).val))‖ ≤
      (bulkFullMassRatio L E ^ Fintype.card ι-1)*A := by
  rw [bulkProductPrior_cmean_eq_retained_grid, bulkGridMean, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : BulkPrimeTuple ι L,
        ‖(bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val)-
          (if bulkTupleRetained L E p then
            (bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p : BulkPrimeTuple ι L,
        (if bulkTupleRetained L E p then 0 else bulkTupleWeight L E p)*A := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases ht : bulkTupleRetained L E p
      · simp only [ite_eq_left ht, sub_self, norm_zero, zero_mul, le_refl]
      · simp only [ite_eq_right ht, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (bulkTupleWeight_nonneg L E p)]
        exact mul_le_mul_of_nonneg_left (hF p) (bulkTupleWeight_nonneg L E p)
    _ = _ := by rw [← Finset.sum_mul, bulkTupleWeight_discarded_sum L E hZ]

theorem bulkGridMean_sub_source_cmean_le_cap (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℂ)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple ι L, ‖F (fun i => (p i).val)‖ ≤ A) :
    ‖bulkGridMean L E F-
      (bulkProductPrior (ι := ι) L E hZ).cmean (fun p => F (fun i => (p i).val))‖ ≤
      ((1+bulkRestorationCap L E) ^ Fintype.card ι-1)*A := by
  apply (bulkGridMean_sub_source_cmean_le L E hZ F hA hF).trans
  apply mul_le_mul_of_nonneg_right _ hA
  apply sub_le_sub_right
  exact pow_le_pow_left₀ ((bulkFullMassRatio_bounds L E hZ).1.trans' zero_le_one)
    (bulkFullMassRatio_bounds L E hZ).2 _

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
