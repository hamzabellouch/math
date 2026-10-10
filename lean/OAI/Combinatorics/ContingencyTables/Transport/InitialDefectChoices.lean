import OAI.Combinatorics.ContingencyTables.Transport.InitialTransversals

namespace OAI

/-!
# Actual remaining label choices for an initial defect

The hole and full pair are removed before the remaining row labels are
chosen. This gives the finite combinatorial space underlying the exact
local initialization brackets, including two removed labels in one cell.
-/

namespace ContingencyTables.InitialDefectChoices

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates
open InitialTransversals (Copy)

variable {C : Type*} [Fintype C] (b : C → ℕ) (p q : Copy b)

@[reducible] def Local (c : C) :=
  {k : Fin (b c) // (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q}

noncomputable def encode (S : (c : C) → Finset (Local b p q c)) : Set (Copy b×Bool) :=
  fun a => if a.1=q then True else if h : a.1≠p ∧ a.1≠q then
    if a.2 then (⟨a.1.2,h⟩:Local b p q a.1.1)∉S a.1.1
      else (⟨a.1.2,h⟩:Local b p q a.1.1)∈S a.1.1
    else False

omit [Fintype C] in
lemma encode_full (S : (c : C) → Finset (Local b p q c)) (t : Bool) :
    (q,t)∈encode b p q S := by
  change (if q=q then True else _) 
  simp

omit [Fintype C] in
lemma encode_hole (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (t : Bool) :
    (p,t)∉encode b p q S := by
  change ¬(if p=q then True else if h : p≠p ∧ p≠q then _ else False)
  simp [hpq]

omit [Fintype C] in
lemma encode_false (S : (c : C) → Finset (Local b p q c)) (a : Copy b)
    (ha : a≠p ∧ a≠q) :
    (a,false)∈encode b p q S ↔ (⟨a.2,ha⟩:Local b p q a.1)∈S a.1 := by
  change (if a=q then True else if h : a≠p ∧ a≠q then _ else False)↔_
  simp [ha]

omit [Fintype C] in
lemma encode_true (S : (c : C) → Finset (Local b p q c)) (a : Copy b)
    (ha : a≠p ∧ a≠q) :
    (a,true)∈encode b p q S ↔ (⟨a.2,ha⟩:Local b p q a.1)∉S a.1 := by
  change (if a=q then True else if h : a≠p ∧ a≠q then _ else False)↔_
  simp [ha]

lemma encode_defect (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) :
    DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q) (encode b p q S) := by
  refine ⟨pair_mem p,pair_mem q,(fun h => hpq (pair_injective h)),?_,?_,?_⟩
  · exact ⟨encode_hole b p q hpq S false,encode_hole b p q hpq S true⟩
  · exact ⟨encode_full b p q S false,encode_full b p q S true⟩
  · intro t ht htp htq
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp (show t∈Finset.univ.toList.map TwoLiftStates.pair from ht)
    have ha : a≠p ∧ a≠q := ⟨fun h => htp (congrArg TwoLiftStates.pair h),
      fun h => htq (congrArg TwoLiftStates.pair h)⟩
    by_cases hs : (⟨a.2,ha⟩:Local b p q a.1)∈S a.1
    · exact Or.inl ⟨(encode_false b p q S a ha).mpr hs,
        fun h => (encode_true b p q S a ha).mp h hs⟩
    · exact Or.inr ⟨(encode_true b p q S a ha).mpr hs,
        fun h => hs ((encode_false b p q S a ha).mp h)⟩

noncomputable def defectEquivChoices (hpq : p≠q) :
    {S : Set (Copy b×Bool) // DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q) S} ≃
      ((c : C) → Finset (Local b p q c)) where
  toFun S c := Finset.univ.filter (fun k => ((⟨c,k.val⟩,false):Copy b×Bool)∈S.val)
  invFun S := ⟨encode b p q S,encode_defect b p q hpq S⟩
  left_inv S := by
    apply Subtype.ext
    ext ⟨a,t⟩
    let R : (c : C) → Finset (Local b p q c) :=
      fun c => Finset.univ.filter (fun k => ((⟨c,k.val⟩,false):Copy b×Bool)∈S.val)
    change (a,t)∈encode b p q R ↔ (a,t)∈S.val
    by_cases hap : a=p
    · subst a
      have he := S.property.2.2.2.1
      cases t <;> simp only [TwoLiftStates.pair,PairEmpty] at he
      · exact iff_of_false (encode_hole b p q hpq R false) he.1
      · exact iff_of_false (encode_hole b p q hpq R true) he.2
    · by_cases haq : a=q
      · subst a
        have hf := S.property.2.2.2.2.1
        cases t <;> simp only [TwoLiftStates.pair,PairFull] at hf
        · exact iff_of_true (encode_full b p q R false) hf.1
        · exact iff_of_true (encode_full b p q R true) hf.2
      · have ha : a≠p ∧ a≠q := ⟨hap,haq⟩
        have hs := S.property.2.2.2.2.2 (TwoLiftStates.pair a) (pair_mem a)
          (fun h => hap (pair_injective h)) (fun h => haq (pair_injective h))
        cases t
        · rw [encode_false b p q R a ha]
          simp [R]
        · rw [encode_true b p q R a ha]
          dsimp only [R]
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          rcases hs with ⟨hf,ht⟩|⟨ht,hf⟩ <;>
            simp only [TwoLiftStates.pair] at hf ht <;> tauto
  right_inv S := by
    funext c
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact encode_false b p q S ⟨c,k.val⟩ k.property

omit [Fintype C] in
lemma fiber_eq_sum (c : C) (a : Copy b) :
    (∑ k : Fin (b c), if (⟨c,k⟩:Copy b)=a then (1:ℕ) else 0)=
      if a.1=c then 1 else 0 := by
  rcases a with ⟨a,k⟩
  by_cases ha : a=c
  · subst a
    simp
  · have hn (k' : Fin (b c)) : (⟨c,k'⟩:Copy b)≠⟨a,k⟩ :=
      fun h => ha (congrArg Sigma.fst h).symm
    simp [ha,hn]

omit [Fintype C] in
/-- There are exactly b-u-v remaining labels in each cell. This proof
uses distinct physical labels, so the coinciding-cell case is included. -/
theorem local_card_balance (hpq : p≠q) (c : C) :
    Fintype.card (Local b p q c)+(if p.1=c then 1 else 0)+(if q.1=c then 1 else 0)=b c := by
  have ht (k : Fin (b c)) :
      (if (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q then (1:ℕ) else 0)+
        (if (⟨c,k⟩:Copy b)=p then 1 else 0)+
        (if (⟨c,k⟩:Copy b)=q then 1 else 0)=1 := by
    by_cases hp : (⟨c,k⟩:Copy b)=p
    · have hq : (⟨c,k⟩:Copy b)≠q := fun h => hpq (hp.symm.trans h)
      simp [hp,hpq]
    · by_cases hq : (⟨c,k⟩:Copy b)=q <;> simp [hp,hq,Ne.symm hpq]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => ht k)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,fiber_eq_sum,fiber_eq_sum] at hs
  have he : (∑ k : Fin (b c), if (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q then (1:ℕ) else 0)=
      Fintype.card (Local b p q c) := by
    rw [Fintype.card_subtype]
    simp
  rw [he] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
  exact hs

omit [Fintype C] in
lemma local_card (hpq : p≠q) (c : C) :
    Fintype.card (Local b p q c)=b c-(if p.1=c then 1 else 0)-(if q.1=c then 1 else 0) := by
  have h := local_card_balance b p q hpq c
  omega

noncomputable def chosen (S : (c : C) → Finset (Local b p q c)) (c : C) : Finset (Fin (b c)) :=
  (S c).map ⟨Subtype.val,Subtype.val_injective⟩

omit [Fintype C] in
lemma chosen_ne (S : (c : C) → Finset (Local b p q c)) (c : C) (k : Fin (b c))
    (hk : k∈chosen b p q S c) : (⟨c,k⟩:Copy b)≠p ∧ (⟨c,k⟩:Copy b)≠q := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hk
  exact a.property

omit [Fintype C] in
lemma encode_row (S : (c : C) → Finset (Local b p q c)) (a : Copy b) :
    (a,false)∈encode b p q S ↔ a=q ∨ a.2∈chosen b p q S a.1 := by
  by_cases haq : a=q
  · exact iff_of_true (haq ▸ encode_full b p q S false) (Or.inl haq)
  · by_cases hap : a=p
    · subst a
      have hn : p.2∉chosen b p q S p.1 := fun h => (chosen_ne b p q S _ _ h).1 rfl
      exact iff_of_false (encode_hole b p q haq S false) (by simp [haq,hn])
    · rw [encode_false b p q S a ⟨hap,haq⟩]
      simp only [haq,false_or,chosen,Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨a.2,hap,haq⟩,h,rfl⟩
      · rintro ⟨k,hk,he⟩
        have he' : k=⟨a.2,hap,haq⟩ := Subtype.ext he
        rwa [he'] at hk

lemma row_count (_hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (c : C) :
    viewCount (InitialTransversals.cell b) (encode b p q S) c false=
      (S c).card+(if q.1=c then 1 else 0) := by
  unfold viewCount
  rw [Fintype.sum_sigma]
  have hi (x : C) :
      (∑ k : Fin (b x), if InitialTransversals.cell b ⟨x,k⟩=c ∧
        ((⟨x,k⟩,false):Copy b×Bool)∈encode b p q S then (1:ℕ) else 0)=
        if x=c then (S c).card+(if q.1=c then 1 else 0) else 0 := by
    by_cases hx : x=c
    · subst x
      simp only [InitialTransversals.cell,true_and,encode_row]
      have he (k : Fin (b c)) :
          (if (⟨c,k⟩:Copy b)=q ∨ k∈chosen b p q S c then (1:ℕ) else 0)=
            (if k∈chosen b p q S c then 1 else 0)+(if (⟨c,k⟩:Copy b)=q then 1 else 0) := by
        by_cases hq : (⟨c,k⟩:Copy b)=q
        · have hn : k∉chosen b p q S c := fun h => (chosen_ne b p q S c k h).2 hq
          simp [hq,hn]
        · by_cases hk : k∈chosen b p q S c <;> simp [hq,hk]
      simp_rw [he]
      rw [Finset.sum_add_distrib,fiber_eq_sum]
      simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [chosen,Finset.card_map]
      simp
    · simp [hx]
  calc
    _ = ∑ x : C, if x=c then (S c).card+(if q.1=c then 1 else 0) else 0 :=
      Finset.sum_congr rfl (fun x _ => hi x)
    _ = _ := by simp

lemma column_count (hpq : p≠q) (S : (c : C) → Finset (Local b p q c)) (c : C) :
    viewCount (InitialTransversals.cell b) (encode b p q S) c true=
      Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0) := by
  have h := defect_counts (InitialTransversals.cell b) (encode b p q S) p q
    (encode_defect b p q hpq S) c
  rw [row_count b p q hpq,InitialTransversals.width_cell] at h
  have hc := local_card_balance b p q hpq c
  have hS := Finset.card_le_univ (S c)
  simp only [InitialTransversals.cell] at h
  omega

noncomputable def localWeight (c : C) (S : Finset (Local b p q c)) : ℝ :=
  (((S.card+(if q.1=c then 1 else 0)).factorial:ℝ)*
    ((Fintype.card (Local b p q c)-S.card+(if q.1=c then 1 else 0)).factorial:ℝ))/(b c).factorial

omit [Fintype C] in
lemma sum_localWeight (hpq : p≠q) (c : C) :
    (∑ S : Finset (Local b p q c),localWeight b p q c S)=
      InitializationBrackets.bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0) := by
  have h := Finset.sum_powerset_apply_card
    (fun k => (((k+(if q.1=c then 1 else 0)).factorial:ℝ)*
      ((Fintype.card (Local b p q c)-k+(if q.1=c then 1 else 0)).factorial:ℝ))/(b c).factorial)
    (x := (Finset.univ : Finset (Local b p q c)))
  simpa [localWeight,InitializationBrackets.bracket,local_card b p q hpq,
    nsmul_eq_mul,Finset.sum_div,mul_div_assoc,mul_assoc] using h

lemma firstLift_encode (hpq : p≠q) (M : ℝ) (S : (c : C) → Finset (Local b p q c)) :
    LabelledFactorial.firstLift (group (InitialTransversals.cell b)) (fun _ => M)
      (InitialTransversals.denominator b) (encode b p q S)=M*∏ c,localWeight b p q c (S c) := by
  unfold LabelledFactorial.firstLift FactorialSignatures.factorialProduct InitialTransversals.denominator
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,groupCount_eq_viewCount,row_count b p q hpq,column_count b p q hpq]
  unfold localWeight
  rw [Finset.prod_div_distrib]
  have he : (∏ c, ((Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0)).factorial:ℝ)*
      (((S c).card+(if q.1=c then 1 else 0)).factorial:ℝ))=
      ∏ c, (((S c).card+(if q.1=c then 1 else 0)).factorial:ℝ)*
        ((Fintype.card (Local b p q c)-(S c).card+(if q.1=c then 1 else 0)).factorial:ℝ) := by
    apply Finset.prod_congr rfl
    intro c _
    exact mul_comm _ _
  rw [he]
  ring

/-- The source bracket product is the actual finite defect normalizer,
with no assumption about where its missing and full labels lie. -/
theorem slotDefect_constant (hpq : p≠q) (M : ℝ) :
    slotDefect pairs (LabelledFactorial.firstLift (group (InitialTransversals.cell b))
      (fun _ => M) (InitialTransversals.denominator b)) ∅ (TwoLiftStates.pair p) (TwoLiftStates.pair q)=
      M*∏ c,InitializationBrackets.bracket (b c) (if p.1=c then 1 else 0) (if q.1=c then 1 else 0) := by
  rw [slotDefect_eq_defect_sum pairs PairedLabels.fresh PairedLabels.cover _
    (TwoLiftStates.pair p) (TwoLiftStates.pair q) (pair_mem p) (pair_mem q)
    (fun h => hpq (pair_injective h))]
  rw [Finset.sum_subtype (p := DefectState pairs (TwoLiftStates.pair p) (TwoLiftStates.pair q)) _
    (by intro S; simp)]
  calc
    _ = ∑ S : ((c : C) → Finset (Local b p q c)),M*∏ c,localWeight b p q c (S c) := by
      apply Fintype.sum_equiv (defectEquivChoices b p q hpq)
      intro S
      have h := firstLift_encode b p q hpq M ((defectEquivChoices b p q hpq) S)
      have he : encode b p q ((defectEquivChoices b p q hpq) S)=S.val :=
        congrArg Subtype.val ((defectEquivChoices b p q hpq).symm_apply_apply S)
      rwa [he] at h
    _ = _ := by
      rw [← Finset.mul_sum,← Fintype.prod_sum]
      simp_rw [sum_localWeight b p q hpq]

end ContingencyTables.InitialDefectChoices

end OAI
