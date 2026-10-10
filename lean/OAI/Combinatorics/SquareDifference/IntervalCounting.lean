import OAI.Combinatorics.SquareDifference.IntervalLift

namespace OAI

section

open Finset

open scoped BigOperators

namespace LiftAnalysis

namespace SquareDifference

open Finset

section SupportCounting

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime] (hinj : Function.Injective p)

include hinj

omit hinj in
lemma primeProduct_injective {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))]
    (hinj : Function.Injective p) : Function.Injective (fun U : Finset J => ∏j∈U,p j) := by
  intro U W he
  dsimp only at he
  apply subset_antisymm
  all_goals intro j hj
  · have hjd : p j∣∏i∈W,p i := by rw [←he]; exact dvd_prod_of_mem p hj
    obtain ⟨i,hi,hji⟩ := ((Fact.out : (p j).Prime).prime.dvd_finsetProd_iff p).mp hjd
    have heq : p j=p i := ((Fact.out : (p i).Prime).eq_one_or_self_of_dvd (p j) hji).resolve_left
      (Fact.out : (p j).Prime).ne_one
    simpa only [hinj heq] using hi
  · have hjd : p j∣∏i∈U,p i := by rw [he]; exact dvd_prod_of_mem p hj
    obtain ⟨i,hi,hji⟩ := ((Fact.out : (p j).Prime).prime.dvd_finsetProd_iff p).mp hjd
    have heq : p j=p i := ((Fact.out : (p i).Prime).eq_one_or_self_of_dvd (p j) hji).resolve_left
      (Fact.out : (p j).Prime).ne_one
    simpa only [hinj heq] using hi

lemma supportFamily_card_le (Q : ℕ) : (supportFamily p Q).card≤Q := by
  calc
    _ ≤ (Icc 1 Q).card := card_le_card_of_injOn (fun U => ∏j∈U,p j)
      (fun U hU => mem_Icc.mpr ⟨primeProduct_pos p U,(mem_filter.mp hU).2⟩)
      (primeProduct_injective p hinj).injOn
    _ ≤ Q := by simp

omit hinj in
lemma liftPiece_sup {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))]
    (_ : Function.Injective p) (L : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n<L,|f n|≤M) (U : Finset J) (x : ResidueSpace p) :
    |liftPiece p L f U x|≤M*(∏j∈U,p j : ℝ) := by
  unfold liftPiece
  rw [abs_mul,abs_inv,abs_of_nonneg (Nat.cast_nonneg L)]
  by_cases hL : L=0
  · rw [hL,Nat.cast_zero,inv_zero,zero_mul]; positivity
  have hg (z : ResidueSpace p) : |exactGate p U z|≤(∏j∈U,p j : ℝ) := by
    rw [exactGate,abs_prod]
    apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
    intro j hj
    unfold residueGate
    split_ifs
    · have hjp : (1:ℝ)≤p j := by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le
      rw [abs_of_nonneg (sub_nonneg.mpr hjp)]
      linarith
    · simpa only [zero_sub,abs_neg,abs_one] using (show (1:ℝ)≤p j by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)
  have hs : |∑n∈range L,f n*exactGate p U (x-fun j => (n:ZMod (p j)))|≤
      (L:ℝ)*(M*(∏j∈U,p j : ℝ)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans (sum_le_sum (fun n hn => ?_))
    · rw [sum_const,card_range,nsmul_eq_mul]
    · rw [abs_mul]
      exact mul_le_mul (hf n (mem_range.mp hn)) (hg _) (abs_nonneg _) hM
  exact le_trans (mul_le_mul_of_nonneg_left hs (by positivity)) (by
    rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hL),one_mul])

end SupportCounting

end SquareDifference

end LiftAnalysis

namespace SquareDifference

open LiftTheory.SquareDifference

section Counting

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma liftSupportFamily_card_le (hinj : Function.Injective p) (Q : ℕ) : (liftSupportFamily p Q).card≤Q :=
  LiftAnalysis.SquareDifference.supportFamily_card_le p hinj Q

lemma intervalPiece_sup (hinj : Function.Injective p) (a L : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n,|f n|≤M) (U : Finset J) (x : ResidueSpace p) :
    |intervalPiece p a L f U x|≤M*(∏j∈U,p j:ℝ) := by
  rw [intervalPiece_shift]
  exact LiftAnalysis.SquareDifference.liftPiece_sup p hinj L _ M hM (fun n _ => hf _) U _

end Counting

end SquareDifference

end

end OAI
