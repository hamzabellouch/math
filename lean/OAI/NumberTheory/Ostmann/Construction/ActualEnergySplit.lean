import OAI.NumberTheory.Ostmann.Construction.RemainingDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem FinitePrior.real_complex_split {α : Type*} [Fintype α] (μ : FinitePrior α)
    (A D : α→ℝ) (B : α→ℂ) (h : ∀x,(A x:ℂ)=(D x:ℂ)+B x) :
    (μ.mean A:ℂ)=(μ.mean D:ℂ)+μ.cmean B := by
  simp only [FinitePrior.mean,FinitePrior.cmean,Complex.ofReal_sum,Complex.ofReal_mul,
    ←Finset.sum_add_distrib,←mul_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x]

theorem real_complex_weighted_sum_split {α : Type*} (S : Finset α)
    (w A D : α→ℝ) (B : α→ℂ) (h : ∀x∈S,(A x:ℂ)=(D x:ℂ)+B x) :
    ((∑x∈S,w x*A x:ℝ):ℂ)=((∑x∈S,w x*D x:ℝ):ℂ)+∑x∈S,(w x:ℂ)*B x := by
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,←Finset.sum_add_distrib,←mul_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x hx]

section
variable (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource) (m : ℕ)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (l : ℕ)

def extendedDiagonal : ℝ :=
  (spectatorPrior spectator m).mean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mean (fun u =>
      ∑p∈integerPivotCell G,
        (((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℝ)*
          Ostmann.smoothPartition (Real.log p-G)*
            remainingDiagonal d P sources seed V giant X G bins (spectatorList spectator ds) l p u))

def extendedOffDiagonal : ℂ :=
  (spectatorPrior spectator m).cmean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).cmean (fun u =>
      ∑p∈integerPivotCell G,
        ((((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℝ)*
          Ostmann.smoothPartition (Real.log p-G):ℂ)*
            remainingOffDiagonal d P sources seed V giant X G bins (spectatorList spectator ds) l p u))

theorem extendedDiagonal_nonneg : 0≤extendedDiagonal d P sources seed V giant spectator m X G bins l := by
  apply FinitePrior.mean_nonneg
  intro ds
  apply FinitePrior.mean_nonneg
  intro u
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Ostmann.smoothPartition_nonneg _))
    (remainingDiagonal_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem extendedRowEnergy_split :
    (extendedRowEnergy d P sources seed V giant spectator m X G bins l:ℂ)=
      (extendedDiagonal d P sources seed V giant spectator m X G bins l:ℂ)+
      extendedOffDiagonal d P sources seed V giant spectator m X G bins l := by
  unfold extendedRowEnergy extendedDiagonal extendedOffDiagonal
  apply FinitePrior.real_complex_split
  intro ds
  apply FinitePrior.real_complex_split
  intro u
  simp only [←Complex.ofReal_mul]
  apply real_complex_weighted_sum_split
  intro p hp
  have hp0 : 0<p := (Finset.mem_Ioc.mp hp).1
  let : NeZero p := ⟨hp0.ne'⟩
  exact remainingRowSquare_split d P sources seed V giant X G bins (spectatorList spectator ds) l p u
end

end Ostmann.Construction

end

end OAI
