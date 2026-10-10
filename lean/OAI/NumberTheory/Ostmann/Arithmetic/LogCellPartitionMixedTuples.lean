import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionIntegers
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionMixed
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionTuples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open IntegerCell PrimeCellReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_mixedTuples_eq_sum_assigned {A : Type*} [AddCommMonoid A]
    (NI : ℕ) (N : ι → ℕ) (loI hiI ηI : ℝ) (lo hi η : ι → ℝ)
    (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i) (F : ℕ → (ι → ℕ) → A) :
    (∑ n ∈ cellSupport NI loI hiI, ∑ p : PrimeCellTuple N lo hi, F n (fun i => (p i).val)) =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
          ∑ p : AssignedPrimeTuple N lo hi η j.2, F n (fun i => (p i).val) := by
  classical
  rw [← sum_assignedIntegerSupport NI loI hiI ηI hI]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [sum_primeTuples_eq_sum_assigned N lo hi η h]
  exact Finset.sum_comm

theorem sum_mixed_prior_eq_sum_assigned
    (NI : ℕ) (N : ι → ℕ) (loI hiI ηI G : ℝ) (φ : ℝ → ℝ) (lo hi η Z : ι → ℝ)
    (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i) (F : ℕ → (ι → ℕ) → ℂ) :
    (∑ n ∈ cellSupport NI loI hiI, ∑ p : PrimeCellTuple N lo hi,
      ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ) *
        (∏ i, (((Z i*(p i).val)⁻¹:ℝ):ℂ)) * F n (fun i => (p i).val)) =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        ∑ n ∈ assignedIntegerSupport NI loI hiI ηI j.1,
          ∑ p : AssignedPrimeTuple N lo hi η j.2,
            ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ) *
              (∏ i, (((Z i*(p i).val)⁻¹:ℝ):ℂ)) * F n (fun i => (p i).val) :=
  sum_mixedTuples_eq_sum_assigned NI N loI hiI ηI lo hi η hI h
    (fun n p => ((Real.exp (-G)*φ (Real.log n-G):ℝ):ℂ) *
      (∏ i, (((Z i*p i)⁻¹:ℝ):ℂ)) * F n p)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
