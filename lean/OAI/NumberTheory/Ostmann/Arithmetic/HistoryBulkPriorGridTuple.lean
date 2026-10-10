import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridMass
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionTuples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement LogCellPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BulkPrimeTuple (ι : Type*) (L : ℝ) :=
  PrimeCellTuple (fun _ : ι => bulkPrimeCutoff L)
    (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L)

def bulkTupleRetained (L : ℝ) (E : Finset ℕ) (p : BulkPrimeTuple ι L) : Prop :=
  ∀ i, (p i).val ∈ bulkPrimeBand L E

def bulkTupleWeight (L : ℝ) (E : Finset ℕ) (p : BulkPrimeTuple ι L) : ℝ :=
  ∏ i, bulkWeight L E (p i).val

def bulkGridMean (L : ℝ) (E : Finset ℕ) (F : (ι → ℕ) → ℂ) : ℂ :=
  ∑ p : BulkPrimeTuple ι L, (bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val)

def bulkProductPrior (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) :
    FinitePrior (ι → (bulkPrimeSource L E hZ).Sample) :=
  dependentProductPrior (fun _ : ι => (bulkPrimeSource L E hZ).law)

def bulkRetainedTupleEquiv (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) :
    (ι → (bulkPrimeSource L E hZ).Sample) ≃
      {p : BulkPrimeTuple ι L // bulkTupleRetained L E p} where
  toFun p := ⟨fun i => ⟨(p i).val, bulkPrimeBand_subset_closed L E (p i).property⟩,
    fun i => (p i).property⟩
  invFun p i := ⟨(p.val i).val, p.property i⟩
  left_inv _p := rfl
  right_inv _p := rfl

theorem bulkProductPrior_cmean_eq_retained_grid (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℂ) :
    (bulkProductPrior (ι := ι) L E hZ).cmean (fun p => F (fun i => (p i).val)) =
      ∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then
        (bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val) else 0 := by
  unfold FinitePrior.cmean
  have he := Fintype.sum_equiv (bulkRetainedTupleEquiv (ι := ι) L E hZ)
    (fun p => ((bulkProductPrior L E hZ).mass p : ℂ)*F (fun i => (p i).val))
    (fun p => (bulkTupleWeight L E p.val : ℂ)*F (fun i => (p.val i).val)) (by
      intro p
      congr 1
      simp only [bulkProductPrior, dependentProductPrior, bulkSource_mass,
        bulkTupleWeight, bulkRetainedTupleEquiv]
      rfl)
  rw [he]
  simpa [Finset.sum_filter] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := bulkTupleRetained L E)
      (fun p => (bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val)))

theorem bulkGridMean_eq_assigned (L : ℝ) (E : Finset ℕ) (hL : 0 ≤ L)
    (η : ι → ℝ) (F : (ι → ℕ) → ℂ) :
    bulkGridMean L E F =
      ∑ j : GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L) η,
        ∑ p : AssignedPrimeTuple (fun _ : ι => bulkPrimeCutoff L)
          (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) η j,
          (∏ i, (((bulkNormalizer L E*(p i).val)⁻¹ : ℝ) : ℂ))*F (fun i => (p i).val) := by
  have hle : bulkLogLower L ≤ bulkLogUpper L := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [bulkGridMean, bulkTupleWeight, bulkWeight, Complex.ofReal_prod] using
    sum_product_prime_prior_eq_sum_assigned
      (fun _ : ι => bulkPrimeCutoff L) (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L)
      η (fun _ => bulkNormalizer L E) (fun _ => hle) F

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
