import OAI.NumberTheory.Ostmann.Construction.JoinedFrame
import OAI.NumberTheory.Ostmann.Construction.RemainingDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

theorem rational_tag_eq_iff_reversal_zero (v w : ℤ) (Hp Hm : ℕ)
    (hp : 0<Hp) (hm : 0<Hm) :
    (w:ℚ)/(Hm:ℚ)=(v:ℚ)/(Hp:ℚ) ↔ Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=0 := by
  rw [div_eq_div_iff (by exact_mod_cast hm.ne' : (Hm:ℚ)≠0)
    (by exact_mod_cast hp.ne' : (Hp:ℚ)≠0)]
  unfold Arithmetic.reversalNumerator
  rw [sub_eq_zero,eq_comm]
  constructor <;> intro h <;> exact_mod_cast h

theorem remaining_pair_offDiagonal_test (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) :
    let f := remainingIntegrand d P sources seed V giant X G bins outside l p u
    let row := remainingTermModularTag sources seed V giant l p u
    let rat := remainingTermExactTag sources seed V giant l
    let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
    (if row (y,w)=row (x,v) ∧ rat (y,w)≠rat (x,v) then f x v*conj (f y w) else 0)=
      if ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ)∣N ∧ N≠0
        then f x v*conj (f y w) else 0 := by
  dsimp only
  by_cases hfx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v=0
  · simp only [hfx,zero_mul,ite_self]
  by_cases hfy : remainingIntegrand d P sources seed V giant X G bins outside l p u y w=0
  · simp only [hfy,map_zero,mul_zero,ite_self]
  have hx := remainingIntegrand_denominator_coprime d P sources seed V giant X G bins outside l p u x v hfx
  have hy := remainingIntegrand_denominator_coprime d P sources seed V giant X G bins outside l p u y w hfy
  have hrow := (modFraction_eq_iff_reversal_dvd _ _ _ v.val w.val hx hy)
  have hrat := rational_tag_eq_iff_reversal_zero v.val w.val _ _
    (remainingProduct_pos sources _ giant x) (remainingProduct_pos sources _ giant y)
  have hr' := Iff.trans eq_comm hrow
  have he :
      (remainingTermModularTag sources seed V giant l p u (y,w)=
          remainingTermModularTag sources seed V giant l p u (x,v) ∧
        remainingTermExactTag sources seed V giant l (y,w)≠remainingTermExactTag sources seed V giant l (x,v)) ↔
      (((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ)∣
          joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val ∧
        joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val≠0) := by
    simpa only [remainingTermModularTag,remainingTermExactTag,remainingExactTag,joinedNumerator,
      halfProduct,Nat.cast_mul,mul_comm (p:ℤ)] using (and_congr hr' (not_congr hrat))
  simp only [he]

theorem refinedRowOffDiagonal_counted {α β τ κ : Type*} [Fintype α] [Fintype β]
    [DecidableEq τ] [DecidableEq κ] (μ : FinitePrior α) (row : α×β→τ)
    (rat : α×β→κ) (f : α→β→ℂ) :
    refinedRowOffDiagonal (fun z : α×β => μ.mass z.1) row rat (fun z => f z.1 z.2)=
      μ.cmean (fun x => μ.cmean (fun y => ∑v,∑w,
        if row (y,w)=row (x,v) ∧ rat (y,w)≠rat (x,v) then f x v*conj (f y w) else 0)) := by
  unfold refinedRowOffDiagonal
  simp only [Fintype.sum_prod_type,FinitePrior.cmean,Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> ring

theorem remainingOffDiagonal_expansion (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) :
    remainingOffDiagonal d P sources seed V giant X G bins outside l p u=
      (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun x =>
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun y =>
          ∑v:AllowedFrequency V l,∑w:AllowedFrequency V l,
            let N := joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val
            if ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ)∣N ∧ N≠0 then
              remainingIntegrand d P sources seed V giant X G bins outside l p u x v*
                conj (remainingIntegrand d P sources seed V giant X G bins outside l p u y w) else 0)) := by
  unfold remainingOffDiagonal remainingTermMass remainingTermValue
  rw [refinedRowOffDiagonal_counted]
  apply congrArg (FinitePrior.cmean (remainingPrior sources
    (Template.remainder (l+1) (Template.current seed l)) giant))
  funext x
  apply congrArg (FinitePrior.cmean (remainingPrior sources
    (Template.remainder (l+1) (Template.current seed l)) giant))
  funext y
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  exact remaining_pair_offDiagonal_test d P sources seed V giant X G bins outside l p u x y v w

end Ostmann.Construction

end

end OAI
