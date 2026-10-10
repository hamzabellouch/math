import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionBoxes
import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionPrimes
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacementPrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeProgression PrimeCellReplacement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev AssignedPrimeTuple (N : ι → ℕ) (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) :=
  ∀ i, {p : ℕ // p ∈ assignedPrimeSupport (N i) (lo i) (hi i) (η i) (j i)}

def assignedTupleEquiv (N : ι → ℕ) (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i) :
    (Σ j : GridBoxIndex lo hi η, AssignedPrimeTuple N lo hi η j) ≃ PrimeCellTuple N lo hi :=
  Equiv.ofBijective
    (fun x i => ⟨(x.2 i).val,assignedPrimeSupport_subset (h i) (x.1 i) (x.2 i).property⟩) (by
      constructor
      · rintro ⟨j,p⟩ ⟨k,q⟩ he
        have hv (i : ι) : (p i).val=(q i).val := congrArg Subtype.val (congrFun he i)
        have hjk : j=k := by
          funext i
          have hu := exists_unique_assignedPrime (η:=η i) (h i)
            (assignedPrimeSupport_subset (h i) (j i) (p i).property)
          exact hu.unique (p i).property (by rw [hv i]; exact (q i).property)
        cases hjk
        apply congrArg (Sigma.mk j)
        funext i
        exact Subtype.ext (hv i)
      · intro p
        have hc : ∀ i, ∃ j : Fin (gridCount (lo i) (hi i) (η i)),
            (p i).val ∈ assignedPrimeSupport (N i) (lo i) (hi i) (η i) j :=
          fun i => (exists_unique_assignedPrime (η:=η i) (h i) (p i).property).exists
        choose j hj using hc
        refine ⟨⟨j,fun i => ⟨(p i).val,hj i⟩⟩,?_⟩
        funext i
        rfl)

theorem sum_primeTuples_eq_sum_assigned {A : Type*} [AddCommMonoid A]
    (N : ι → ℕ) (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i) (F : (ι → ℕ) → A) :
    (∑ p : PrimeCellTuple N lo hi, F (fun i => (p i).val)) =
      ∑ j : GridBoxIndex lo hi η, ∑ p : AssignedPrimeTuple N lo hi η j, F (fun i => (p i).val) := by
  classical
  have hh := Fintype.sum_equiv (assignedTupleEquiv N lo hi η h)
    (fun x => F (fun i => (x.2 i).val)) (fun p => F (fun i => (p i).val)) (fun x => rfl)
  simpa only [Fintype.sum_sigma] using hh.symm

theorem sum_product_prime_prior_eq_sum_assigned
    (N : ι → ℕ) (lo hi η Z : ι → ℝ) (h : ∀ i, lo i ≤ hi i) (F : (ι → ℕ) → ℂ) :
    (∑ p : PrimeCellTuple N lo hi,
      (∏ i, (((Z i*(p i).val)⁻¹:ℝ):ℂ))*F (fun i => (p i).val)) =
      ∑ j : GridBoxIndex lo hi η, ∑ p : AssignedPrimeTuple N lo hi η j,
        (∏ i, (((Z i*(p i).val)⁻¹:ℝ):ℂ))*F (fun i => (p i).val) :=
  sum_primeTuples_eq_sum_assigned N lo hi η h (fun p => (∏ i, (((Z i*p i)⁻¹:ℝ):ℂ))*F p)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
