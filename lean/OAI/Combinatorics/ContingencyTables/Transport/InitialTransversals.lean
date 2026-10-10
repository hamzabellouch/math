import OAI.Combinatorics.ContingencyTables.Transport.PairedLabels
import OAI.Combinatorics.ContingencyTables.Machines.InitialLocalChoices

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open CommonBasesFPRAS TwoLiftStates LabelledFactorial InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

abbrev Copy := Σ c, Fin (b c)

@[reducible] def cell (p : Copy b) : C := p.1

@[reducible] noncomputable def encode (S : (c : C) → Finset (Fin (b c))) : Set (Copy b×Bool) :=
  fun p => if p.2 then p.1.2∉S p.1.1 else p.1.2∈S p.1.1

omit [Fintype C] in
@[simp] lemma encode_false (S : (c : C) → Finset (Fin (b c))) (p : Copy b) :
    (p,false)∈encode b S ↔ p.2∈S p.1 := Iff.rfl

omit [Fintype C] in
@[simp] lemma encode_true (S : (c : C) → Finset (Fin (b c))) (p : Copy b) :
    (p,true)∈encode b S ↔ p.2∉S p.1 := Iff.rfl

lemma encode_plain (S : (c : C) → Finset (Fin (b c))) : PlainState pairs (encode b S) := by
  intro p hp
  obtain ⟨a,rfl⟩ : ∃ a, TwoLiftStates.pair a=p := by simpa [pairs] using hp
  by_cases hs : a.2∈S a.1
  · exact Or.inl (by simp [TwoLiftStates.pair,hs])
  · exact Or.inr (by simp [TwoLiftStates.pair,hs])

noncomputable def plainEquivChoices :
    {S : Set (Copy b×Bool) // PlainState pairs S} ≃ ((c : C) → Finset (Fin (b c))) where
  toFun S c := Finset.univ.filter (fun k => ((⟨c,k⟩,false):Copy b×Bool)∈S.val)
  invFun S := ⟨encode b S,encode_plain b S⟩
  left_inv S := by
    apply Subtype.ext
    ext ⟨⟨c,k⟩,t⟩
    have h := S.property (TwoLiftStates.pair (⟨c,k⟩:Copy b)) (pair_mem (⟨c,k⟩:Copy b))
    cases t
    · simp
    · simp only [encode_true,Finset.mem_filter,Finset.mem_univ,true_and]
      change (¬((⟨c,k⟩,false):Copy b×Bool)∈S.val)↔((⟨c,k⟩,true):Copy b×Bool)∈S.val
      rcases h with ⟨ha,hb⟩|⟨ha,hb⟩ <;> simp [TwoLiftStates.pair] at ha hb ⊢ <;> tauto
  right_inv S := by
    funext c
    ext k
    simp

lemma width_cell (c : C) : width (cell b) c=b c := by
  rw [width_eq_sum,Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c then 1 else 0)=
        if x=c then b x else 0 := by
    by_cases hx : x=c
    · subst x
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then b x else 0)=b c by simp) using 1
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma row_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c false=(S c).card := by
  unfold viewCount
  rw [Fintype.sum_sigma]
  have hinner (x : C) :
      (∑ k : Fin (b x), if cell b ⟨x,k⟩=c ∧ ((⟨x,k⟩,false):Copy b×Bool)∈encode b S then 1 else 0)=
        if x=c then (S c).card else 0 := by
    by_cases hx : x=c
    · subst x
      simp only [cell,true_and,encode_false]
      simp
    · simp [hx]
  convert (show (∑ x : C, if x=c then (S c).card else 0)=(S c).card by simp) using 1
  apply Finset.sum_congr rfl
  intro x _
  exact hinner x

lemma column_count (S : (c : C) → Finset (Fin (b c))) (c : C) :
    viewCount (cell b) (encode b S) c true=b c-(S c).card := by
  have h := plain_counts (cell b) (encode b S) (encode_plain b S) c
  rw [row_count,width_cell] at h
  omega

noncomputable def denominator : ℝ := ∏ c, ((b c)!:ℝ)

lemma firstLift_encode (M : ℝ) (S : (c : C) → Finset (Fin (b c))) :
    firstLift (group (cell b)) (fun _ => M) (denominator b) (encode b S)=
      M*∏ c, localWeight (b c) 0 0 (S c) := by
  unfold firstLift FactorialSignatures.factorialProduct denominator
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,groupCount_eq_viewCount,row_count,column_count]
  simp only [localWeight,Nat.sub_zero,Nat.add_zero]
  rw [Finset.prod_div_distrib]
  have he : (∏ c, ((b c-(S c).card)!:ℝ)*((S c).card !:ℝ))=
      ∏ c, ((S c).card !:ℝ)*((b c-(S c).card)!:ℝ) := by
    apply Finset.prod_congr rfl
    intro c _
    exact mul_comm _ _
  rw [he]
  ring

/-- The actual paired-transversal total at a constant raw completion
count M is exactly the manuscript's M*product(b+1). -/
theorem slotTotal_constant (M : ℝ) :
    slotTotal pairs (firstLift (group (cell b)) (fun _ => M) (denominator b)) ∅=
      M*∏ c, ((b c:ℝ)+1) := by
  rw [slotTotal_eq_plain_sum pairs PairedLabels.fresh PairedLabels.cover]
  rw [Finset.sum_subtype (p := PlainState (pairs : List ((Copy b×Bool)×(Copy b×Bool)))) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Fin (b c))), M*∏ c, localWeight (b c) 0 0 (S c) := by
      apply Fintype.sum_equiv (plainEquivChoices b)
      intro S
      have h := firstLift_encode b M ((plainEquivChoices b) S)
      have he : encode b ((plainEquivChoices b) S)=S.val :=
        congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply S)
      rwa [he] at h
    _ = _ := by
      rw [← Finset.mul_sum]
      have he := sum_independent_choices b (fun _ => 0) (fun _ => 0)
      simp only [Nat.sub_zero] at he
      rw [he]
      simp_rw [InitializationBrackets.bracket_neither]

end ContingencyTables.InitialTransversals

end OAI
