import OAI.NumberTheory.Ostmann.Construction.ActualEnergySplit
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalNode

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction
namespace FinitePrior

theorem cmean_mul_left {α : Type*} [Fintype α] (μ : FinitePrior α) (c : ℂ) (f : α→ℂ) :
    μ.cmean (fun x => c*f x)=c*μ.cmean f := by
  simp only [cmean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem cmean_sum {α β : Type*} [Fintype α] (μ : FinitePrior α) (S : Finset β) (F : β→α→ℂ) :
    μ.cmean (fun x => ∑b∈S,F b x)=∑b∈S,μ.cmean (F b) := by
  simp only [cmean,Finset.mul_sum]
  exact Finset.sum_comm

theorem pair_pivot_sum {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (μ : FinitePrior α) (S : Finset δ) (w : δ→ℂ) (F : δ→α→α→β→γ→ℂ) :
    (∑p∈S,w p*μ.cmean (fun x => μ.cmean (fun y => ∑v,∑z,F p x y v z)))=
      μ.cmean (fun x => μ.cmean (fun y => ∑v,∑z,∑p∈S,w p*F p x y v z)) := by
  simp_rw [←cmean_mul_left]
  rw [←cmean_sum]
  apply congrArg (cmean μ)
  funext x
  rw [←cmean_sum]
  apply congrArg (cmean μ)
  funext y
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.sum_comm
end FinitePrior

theorem offDiagonal_weighted_pair_expansion (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) :
    (∑p∈integerPivotCell G,
      ((((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℝ)*
        Ostmann.smoothPartition (Real.log p-G):ℂ)*
        remainingOffDiagonal d P sources seed V giant X G bins outside l p u)=
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun x =>
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun y =>
          ∑v:AllowedFrequency V l,∑w:AllowedFrequency V l,∑p∈integerPivotCell G,
            let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
            if ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ)∣N ∧ N≠0
            then pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p else 0)) := by
  simp_rw [remainingOffDiagonal_expansion]
  rw [FinitePrior.pair_pivot_sum]
  apply congrArg (FinitePrior.cmean (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant))
  funext x
  apply congrArg (FinitePrior.cmean (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant))
  funext y
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp only [pivotPairWeight,Complex.ofReal_natCast,mul_zero]
  ring

theorem actualCoefficient_prime_node (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (X G : ℝ) (g : (q:ℕ)→ZMod q→ℂ) (bins : List ℕ→State→ℝ) (outside : List ℕ)
    (l : ℕ) (a : State) (hp : Nat.Prime a.giantPlus) (hm : Nat.Prime a.giantMinus)
    (hV : ∀j≤l,V j<a.giantPlus ∧ V j<a.giantMinus) :
    actualCoefficient sources seed V X G g bins outside (l+1) a=
      ∑v:AllowedFrequency V l,∑w:AllowedFrequency V l,
        (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).cmean
          (actualNodeTerm sources seed V X G g bins outside l a v w) := by
  exact canonicalCoefficient_prime_node sources seed V outside _ Ostmann.smoothPartition G l a hp hm hV

end Ostmann.Construction

end

end OAI
