import OAI.Combinatorics.ContingencyTables.Transport.InitialTransversals
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialization

namespace OAI

/-!
# Exact binomial/factorial cancellation in a transversal normalizer

Every small integer profile has a product of binomial numbers of label
preimages. Its factorial lift contributes the inverse product, so the
actual transversal normalizer is exactly the raw integer-profile sum.
-/

namespace ContingencyTables.TransversalCount

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialTransversals InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

@[reducible] def Profile := (c : C) → Fin (b c+1)

noncomputable def cardAt (c : C) (S : Finset (Fin (b c))) : Fin (b c+1) :=
  ⟨S.card,by have h := Finset.card_le_univ S; simpa using Nat.lt_succ_of_le h⟩

noncomputable def cardProfile (S : (c : C) → Finset (Fin (b c))) : Profile b :=
  fun c => cardAt b c (S c)

noncomputable def display (x : Profile b) : C×Bool → ℕ :=
  fun u => if u.2 then b u.1-(x u.1).val else (x u.1).val

omit [Fintype C] in
lemma local_fiber (c : C) (x : Fin (b c+1)) :
    (∑ S : Finset (Fin (b c)), if cardAt b c S=x then InitialLocalChoices.localWeight (b c) 0 0 S else 0)=1 := by
  have hx : x.val≤b c := by have := x.isLt; omega
  have h := Finset.sum_powerset_apply_card
    (fun k => if k=x.val then ((k.factorial:ℝ)*((b c-k).factorial:ℝ))/(b c).factorial else 0)
    (x := (Finset.univ : Finset (Fin (b c))))
  have he : (∑ S : Finset (Fin (b c)), if S.card=x.val then
      ((S.card.factorial:ℝ)*((b c-S.card).factorial:ℝ))/(b c).factorial else 0)=
      ((b c).choose x.val:ℝ)*((x.val.factorial:ℝ)*((b c-x.val).factorial:ℝ))/(b c).factorial := by
    simpa [nsmul_eq_mul,mul_ite,mul_div_assoc,Finset.mem_range,show x.val<b c+1 by omega] using h
  have hf : ((b c).choose x.val:ℝ)*(x.val.factorial:ℝ)*((b c-x.val).factorial:ℝ)=((b c).factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hx
  calc
    _ = ∑ S : Finset (Fin (b c)), if S.card=x.val then
        ((S.card.factorial:ℝ)*((b c-S.card).factorial:ℝ))/(b c).factorial else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      simp only [cardAt,Fin.ext_iff,InitialLocalChoices.localWeight,Nat.sub_zero,Nat.add_zero]
    _ = _ := he
    _ = 1 := by rw [← mul_assoc,hf]; exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

lemma profile_fiber (x : Profile b) :
    (∑ S : ((c : C) → Finset (Fin (b c))),if cardProfile b S=x then
      ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) else 0)=1 := by
  calc
    _ = ∏ c,∑ S : Finset (Fin (b c)),if cardAt b c S=x c then
          InitialLocalChoices.localWeight (b c) 0 0 S else 0 := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Fintype.prod_ite_zero]
      congr 1
      exact propext funext_iff
    _ = ∏ _c : C,(1:ℝ) := by
      apply Finset.prod_congr rfl
      intro c _
      exact local_fiber b c (x c)
    _ = 1 := by simp

/-- Pushforward of the actual finite labelled-choice weights is counting
measure on the bounded integer profiles. -/
theorem choices_sum (H : Profile b → ℝ) :
    (∑ S : ((c : C) → Finset (Fin (b c))),H (cardProfile b S)*
      ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c))=∑ x : Profile b,H x := by
  calc
    _ = ∑ x : Profile b,H x*∑ S : ((c : C) → Finset (Fin (b c))),
        if cardProfile b S=x then ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      simp [mul_ite]
    _ = _ := by simp_rw [profile_fiber]; simp

lemma count_encode (S : (c : C) → Finset (Fin (b c))) :
    groupCount (group (cell b)) (InitialTransversals.encode b S)=display b (cardProfile b S) := by
  funext u
  rcases u with ⟨c,t⟩
  rw [groupCount_eq_viewCount]
  cases t
  · exact InitialTransversals.row_count b S c
  · exact InitialTransversals.column_count b S c

lemma firstLift_encode (h : (C×Bool → ℕ) → ℝ) (S : (c : C) → Finset (Fin (b c))) :
    firstLift (group (cell b)) h (InitialTransversals.denominator b) (InitialTransversals.encode b S)=
      h (display b (cardProfile b S))*∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) := by
  calc
    _ = firstLift (group (cell b)) (fun _ => h (display b (cardProfile b S)))
        (InitialTransversals.denominator b) (InitialTransversals.encode b S) := by
      unfold firstLift
      rw [count_encode]
    _ = _ := InitialTransversals.firstLift_encode b _ S

/-- The literal factorial lift's transversal normalizer is the original
integer-profile count, for arbitrary raw h and arbitrary capacities. -/
theorem slotTotal_eq_profiles (h : (C×Bool → ℕ) → ℝ) :
    slotTotal pairs (firstLift (group (cell b)) h (InitialTransversals.denominator b)) ∅=
      ∑ x : Profile b,h (display b x) := by
  rw [slotTotal_eq_plain_sum pairs PairedLabels.fresh PairedLabels.cover]
  rw [Finset.sum_subtype (p := PlainState (pairs : List ((Copy b×Bool)×(Copy b×Bool)))) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Fin (b c))),h (display b (cardProfile b S))*
        ∏ c,InitialLocalChoices.localWeight (b c) 0 0 (S c) := by
      apply Fintype.sum_equiv (plainEquivChoices b)
      intro S
      have ht := firstLift_encode b h ((plainEquivChoices b) S)
      have he : InitialTransversals.encode b ((plainEquivChoices b) S)=S.val :=
        congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
      rwa [he] at ht
    _ = _ := choices_sum b (fun x => h (display b x))

end ContingencyTables.TransversalCount

namespace ContingencyTables.CompanionTransversalCount

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionInitialization TwoLiftStates

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Exact binomial/factorial cancellation for the manuscript's literal
softened completion count, including the terminal annealing parameter. -/
theorem total_eq_raw_profiles (A : Instance I J) (alpha : ℝ) :
    slotTotal pairs (f A alpha) ∅=
      ∑ x : TransversalCount.Profile (fun s : SmallCell A => A.b s.val.1 s.val.2),
        h A alpha (TransversalCount.display (fun s : SmallCell A => A.b s.val.1 s.val.2) x) := by
  unfold f
  rw [denominator_eq]
  convert TransversalCount.slotTotal_eq_profiles
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (h A alpha) using 1
  congr 1
  all_goals
    congr 1
    ext
    simp

end ContingencyTables.CompanionTransversalCount

end OAI
