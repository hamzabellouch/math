import OAI.Combinatorics.ContingencyTables.Transport.FiniteMetropolis
import OAI.Combinatorics.ContingencyTables.Transport.DyadicAcceptance
import OAI.Combinatorics.ContingencyTables.Transport.IntegerPropagation

namespace OAI

/-! # Integer transition counts without enumerating acceptance bits -/

namespace ContingencyTables.FiniteAcceptCounts
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

def denominator (K : ℕ) : ℕ := Fintype.card β * 2^K

def offCount (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) (b : α) : ℕ :=
  if b=a then 0 else
    (Finset.univ.filter (fun z => proposal z=some b)).card * 2^(K-gap b)

def row (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) (b : α) : ℕ :=
  offCount a proposal gap K b +
    if b=a then denominator (β := β) K - ∑ x,offCount a proposal gap K x else 0

lemma denominator_pos (K : ℕ) : 0<denominator (β := β) K := by
  unfold denominator
  exact Nat.mul_pos Fintype.card_pos (by positivity)

lemma offCount_mass (a b : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ)
    (hba : b≠a) :
    (offCount a proposal gap K b:ℚ)/denominator (β := β) K =
      (finiteAcceptLaw a proposal (fun b => FairBits.acceptDyadic (gap b) K)).mass b := by
  rw [finiteAcceptLaw_off_diagonal a b proposal _ hba.symm]
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2^K)))
    (FairBits.acceptDyadic (gap b) K) (fun _ => Classical.propDecidable _)]
  rw [FairBits.acceptDyadic_count]
  simp only [offCount,ite_eq_right hba,denominator,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat,Fintype.card_fin]
  exact (div_mul_div_comm
    ((Finset.univ.filter (fun z => proposal z=some b)).card:ℚ)
    (Fintype.card β) (2^(K-gap b)) (2^K)).symm

lemma offCount_sum_le (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) :
    (∑ b,offCount a proposal gap K b) ≤ denominator (β := β) K := by
  let p:=finiteAcceptLaw a proposal (fun b => FairBits.acceptDyadic (gap b) K)
  have hQ : (0:ℚ)<denominator (β := β) K := by exact_mod_cast denominator_pos (β := β) K
  have hb (b : α) : (offCount a proposal gap K b:ℚ)/denominator (β := β) K ≤ p.mass b := by
    by_cases hba : b=a
    · subst b
      simpa only [offCount,ite_true,Nat.cast_zero,zero_div] using p.nonnegative a
    · exact (offCount_mass a b proposal gap K hba).le
  have hs:=Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hb b)
  rw [←Finset.sum_div,←Nat.cast_sum,p.total] at hs
  exact_mod_cast (div_le_one hQ).mp hs

lemma row_total (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) :
    ∑ b,row a proposal gap K b=denominator (β := β) K := by
  simp only [row,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact Nat.add_sub_of_le (offCount_sum_le a proposal gap K)

/-- The diagonal count is recovered from the row total; all other entries
use a proposal count and one binary power, independently of `2^K` coins. -/
theorem row_kernel (a : α) (proposal : α → β → Option α) (gap : α → α → ℕ) (K : ℕ) :
    (IntegerPropagation.kernel (fun a b => row a (proposal a) (gap a) K b)
      (denominator (β := β) K) (denominator_pos K)
      (fun x => row_total x (proposal x) (gap x) K) a) =
      finiteAcceptLaw a (proposal a) (fun b => FairBits.acceptDyadic (gap a b) K) := by
  apply RationalLaw.eq_of_off_diagonal _ _ a
  intro b hba
  change (row a (proposal a) (gap a) K b:ℚ)/denominator (β := β) K=_
  simp only [row,ite_eq_right hba,add_zero]
  exact offCount_mass a b (proposal a) (gap a) K hba

end
end ContingencyTables.FiniteAcceptCounts

end OAI
