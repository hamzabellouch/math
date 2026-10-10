import OAI.NumberTheory.Ostmann.Construction.ActualRowExtraction
import OAI.NumberTheory.Ostmann.Construction.IntegerPivotExtension
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

namespace FinitePrior

theorem mean_comm {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (F : α→β→ℝ) :
    μ.mean (fun x => ν.mean (F x))=ν.mean (fun y => μ.mean (fun x => F x y)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem mean_mul_left {α : Type*} [Fintype α] (μ : FinitePrior α) (c : ℝ) (F : α→ℝ) :
    μ.mean (fun x => c*F x)=c*μ.mean F := by
  simp only [mean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring
end FinitePrior

def remainingRowSquare (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) (p : ℕ) : ℝ :=
  integerPivotSquare
    ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod
    (fun p => remainingRow d P sources seed V giant X G bins outside l p u) p

theorem remainingRowSquare_eq (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (p : ℕ) [NeZero p] :
    remainingRowSquare d P sources seed V giant X G bins outside l u p=
      ∑t,‖remainingRow d P sources seed V giant X G bins outside l p u t‖^2 := by
  have hn := NeZero.ne (halfProduct p (assignedSlots sources
    (Template.extracted (l+1) (Template.current seed l)) u))
  unfold remainingRowSquare integerPivotSquare
  simp only [show p*((assignedSlots sources
    (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod≠0 from hn,dite_false]
  congr 1

def extendedRowEnergy (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource) (m : ℕ)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (l : ℕ) : ℝ :=
  (spectatorPrior spectator m).mean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean (fun u =>
      ∑p∈integerPivotCell G,
        (((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℝ)*
          Ostmann.smoothPartition (Real.log p-G)*
            remainingRowSquare d P sources seed V giant X G bins (spectatorList spectator ds) l u p))

theorem actualAmplitude_integer_row_bound (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (spectator : PrimeSource) (m : ℕ) (X G : ℝ) (hZ : 0<logCellMass G ∅)
    (bins : List ℕ→State→ℝ) (l : ℕ) :
    ‖actualAmplitude sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G
      (residueTransform d) (favorableGiantResidueTransform d P) bins l‖^2 ≤
      Real.exp (-Real.log (logCellMass G ∅))*
        extendedRowEnergy d P sources seed V (logCellPrimeSource G ∅ hZ) spectator m X G bins l := by
  have hprime := actualAmplitude_prime_row_bound d P sources seed V
    (logCellPrimeSource G ∅ hZ) spectator m X G bins l
  simp_rw [←remainingRowSquare_eq] at hprime
  apply hprime.trans
  rw [extendedRowEnergy,←FinitePrior.mean_mul_left]
  apply FinitePrior.mean_mono
  intro ds
  rw [FinitePrior.mean_comm,←FinitePrior.mean_mul_left]
  apply FinitePrior.mean_mono
  intro u
  simp only [halfProduct,Nat.cast_mul,remainingRowSquare]
  convert logCellPrior_extend_square_rows G hZ
    ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod
    (fun p => remainingRow d P sources seed V (logCellPrimeSource G ∅ hZ)
      X G bins (spectatorList spectator ds) l p u) using 1
  unfold FinitePrior.mean
  congr 1

end Ostmann.Construction

end

end OAI
