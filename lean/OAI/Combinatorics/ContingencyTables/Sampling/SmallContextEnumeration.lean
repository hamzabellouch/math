import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextCoordinates
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperContextChildren
import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextCount

namespace OAI

/-! # Physical enumeration of a balanced exposure child

Every later small-cell choice occurs once, with the retained prefix fixed.
The large-cell capacities remain the original capacities throughout.
-/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def splitChoices (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) : Cells small → Fin (U+1) :=
  (Sum.elim τ (Sum.elim (fun _ : Unit => k) y)) ∘ (cellSplitEquiv small s hs).symm

lemma splitChoices_prefix (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) (a : Earlier small s) :
    splitChoices small s hs U τ k y a.val=τ a := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inl a)))=τ a
  rw [Equiv.symm_apply_apply]
  rfl

lemma splitChoices_special (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) :
    splitChoices small s hs U τ k y ⟨s,hs⟩=k := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inr (.inl ()))))=k
  rw [Equiv.symm_apply_apply]
  rfl

lemma splitChoices_later (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) (a : Later small s) :
    splitChoices small s hs U τ k y a.val=y a := by
  change Sum.elim τ (Sum.elim (fun _ : Unit => k) y)
    ((cellSplitEquiv small s hs).symm ((cellSplitEquiv small s hs) (.inr (.inr a))))=y a
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def choiceProfile (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (x : Cells small → Fin (U+1)) : BoundedProfile small B := fun a =>
  ⟨if a.2 then U-(x a.1).val else (x a.1).val,by
    rw [hB _ _ a.1.property]
    cases a.2
    · exact (x a.1).isLt
    · exact Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

omit [LinearOrder I] [LinearOrder J] in
lemma choiceProfile_balanced (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    ∀ i j, smallView small (naturalProfile (choiceProfile small B U hB x)) false i j=
      smallQ small B (naturalProfile (choiceProfile small B U hB x)) i j := by
  intro i j
  cases hij : small i j
  · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
  · simp only [smallView,smallQ,hij,dite_eq_left,naturalProfile,choiceProfile,
      Bool.false_eq_true,↓reduceIte,hB i j hij]
    exact (Nat.sub_sub_self (Nat.le_of_lt_succ (x ⟨(i,j),hij⟩).isLt)).symm

noncomputable def prefixChoices (small : I → J → Bool) (s : I×J)
    (σ : I×J → ℕ) (U : ℕ)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) : Earlier small s → Fin (U+1) :=
  fun a => ⟨σ a.val.val,Nat.lt_succ_of_le (hσ a)⟩

noncomputable def balancedContext (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    (y : Later small s → Fin (U+1)) : BalancedProfiles small B s σ k.val := by
  let x := splitChoices small s hs U (prefixChoices small s σ U hσ) k y
  refine ⟨choiceProfile small B U hB x,choiceProfile_balanced small B U hB x,?_,?_⟩
  · intro i j hij hbefore
    simp only [smallView,hij,dite_eq_left,naturalProfile,choiceProfile,Bool.false_eq_true,↓reduceIte]
    change (x ⟨(i,j),hij⟩).val=σ (i,j)
    exact congrArg Fin.val (splitChoices_prefix small s hs U _ k y ⟨⟨(i,j),hij⟩,hbefore⟩)
  · simp only [smallView,hs,dite_eq_left,naturalProfile,choiceProfile,Bool.false_eq_true,↓reduceIte]
    change (x ⟨s,hs⟩).val=k.val
    exact congrArg Fin.val (splitChoices_special small s hs U _ k y)

lemma balanced_false_determines (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (k : ℕ)
    (x y : BalancedProfiles small B s σ k)
    (he : ∀ a : Cells small, naturalProfile x.val (a,false)=naturalProfile y.val (a,false)) :
    x=y := by
  apply Subtype.ext
  apply naturalProfile_injective small B
  funext a
  rcases a with ⟨a,b⟩
  cases b
  · exact he a
  · have hx := x.property.1 a.val.1 a.val.2
    have hy := y.property.1 a.val.1 a.val.2
    simp only [smallView,smallQ,a.property,dite_eq_left] at hx hy
    change naturalProfile x.val (a,false)=B a.val.1 a.val.2-naturalProfile x.val (a,true) at hx
    change naturalProfile y.val (a,false)=B a.val.1 a.val.2-naturalProfile y.val (a,true) at hy
    have hbX := naturalProfile_bounded x.val (a,true)
    have hbY := naturalProfile_bounded y.val (a,true)
    dsimp only at hbX hbY
    have he' := he a
    omega

noncomputable def suffixChoices (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (k : Fin (U+1))
    (z : BalancedProfiles small B s σ k.val) : Later small s → Fin (U+1) := fun a =>
  ⟨naturalProfile z.val (a.val,false),by
    have h := naturalProfile_bounded z.val (a.val,false)
    rw [hB _ _ a.val.property] at h
    exact Nat.lt_succ_of_le h⟩

noncomputable def balancedContextEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1)) :
    (Later small s → Fin (U+1)) ≃ BalancedProfiles small B s σ k.val where
  toFun := balancedContext small B s hs σ U hB hσ k
  invFun := suffixChoices small B s σ U hB k
  left_inv y := by
    funext a
    apply Fin.ext
    change (splitChoices small s hs U (prefixChoices small s σ U hσ) k y a.val).val=(y a).val
    rw [splitChoices_later]
  right_inv z := by
    apply balanced_false_determines small B s σ k.val
    intro a
    obtain ⟨q,rfl⟩ := (cellSplitEquiv small s hs).surjective a
    rcases q with p|(_|t)
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) p.val).val=naturalProfile z.val (p.val,false)
      rw [splitChoices_prefix]
      simpa only [prefixChoices,smallView,p.val.property,dite_eq_left] using
        (z.property.2.1 _ _ p.val.property p.property).symm
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) ⟨s,hs⟩).val=naturalProfile z.val (⟨s,hs⟩,false)
      rw [splitChoices_special]
      simpa only [smallView,hs,dite_eq_left] using z.property.2.2.symm
    · change (splitChoices small s hs U (prefixChoices small s σ U hσ) k
        (suffixChoices small B s σ U hB k z) t.val).val=naturalProfile z.val (t.val,false)
      rw [splitChoices_later]
      rfl

def prefixRaw (small : I → J → Bool) (s : I×J) (σ : I×J → ℕ) (U : ℕ) :
    Earlier small s×Bool → ℕ := fun a => if a.2 then U-σ a.1.val.val else σ a.1.val.val

noncomputable def reindexChoices {n U : ℕ} (small : I → J → Bool) (s : I×J)
    (e : Fin n ≃ Later small s) :
    (Fin n → Fin (U+1)) ≃ (Later small s → Fin (U+1)) where
  toFun y := y ∘ e.symm
  invFun y := y ∘ e
  left_inv y := by funext a; exact congrArg y (e.symm_apply_apply a)
  right_inv y := by funext a; exact congrArg y (e.apply_symm_apply a)

lemma embedding_coordinate_apply {n : ℕ} (M : Fin n → ℕ) (z : Bool → ℕ)
    (q : Assignments (widths M)) (a : Coordinates Bool (widths M)) :
    embedding (widths M) z q a=
      joinedProfile M z ((assignmentEquiv M) q) (coordinateEquiv Bool M a) := by
  have h := embedding_coordinate M z ((assignmentEquiv M) q) a
  simpa only [Equiv.symm_apply_apply] using h

lemma physical_embedding_eq (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (q : Assignments (widths (fun _ : Fin n => U))) :
    (Sum.elim (prefixRaw small s σ U)
      (embedding (widths (fun _ : Fin n => U)) (childProfile U k.val) q)) ∘
      (contextEquiv small s hs e U).symm=
    naturalProfile (balancedContext small B s hs σ U hB hσ k
      ((reindexChoices small s e) ((assignmentEquiv (fun _ : Fin n => U)) q))).val := by
  funext a
  obtain ⟨v,rfl⟩ := (contextEquiv small s hs e U).surjective a
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  cases v with
  | inl p =>
    rcases p with ⟨p,b⟩
    rw [contextEquiv_prefix]
    change (if b then U-σ p.val.val else σ p.val.val)=
      if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ p.val).val
      else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ p.val).val
    rw [splitChoices_prefix]
    rfl
  | inr v =>
    obtain ⟨w,rfl⟩ := (coordinateEquiv Bool (fun _ : Fin n => U)).symm.surjective v
    cases w with
    | inl b =>
      rw [contextEquiv_special]
      simp only [Sum.elim_inr]
      rw [embedding_coordinate_apply,Equiv.apply_symm_apply]
      change (if b then U-k.val else k.val)=
        if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ ⟨s,hs⟩).val
        else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ ⟨s,hs⟩).val
      rw [splitChoices_special]
    | inr p =>
      rcases p with ⟨i,b⟩
      rw [contextEquiv_later]
      simp only [Sum.elim_inr]
      rw [embedding_coordinate_apply,Equiv.apply_symm_apply]
      change (if b then U-((assignmentEquiv (fun _ : Fin n => U)) q i).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q i).val)=
        if b then U-(splitChoices small s hs U (prefixChoices small s σ U hσ) k _ (e i).val).val
        else (splitChoices small s hs U (prefixChoices small s σ U hσ) k _ (e i).val).val
      rw [splitChoices_later]
      change (if b then U-((assignmentEquiv (fun _ : Fin n => U)) q i).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q i).val)=
        if b then U-((assignmentEquiv (fun _ : Fin n => U)) q (e.symm (e i))).val
        else ((assignmentEquiv (fun _ : Fin n => U)) q (e.symm (e i))).val
      rw [Equiv.symm_apply_apply]

variable [Fintype I] [Fintype J]

/-- The recursive transport child is the literal sum over physical
bounded balanced profiles, retaining every large completion multiplicity. -/
theorem eliminate_context_eq_balanced_mass (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) :
    eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U k.val)=
      ∑ z : BalancedProfiles small B s σ k.val, hardMarginal small B r c L (naturalProfile z.val) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (((assignmentEquiv (fun _ : Fin n => U)).trans
    (reindexChoices small s e)).trans (balancedContextEquiv small B s hs σ U hB hσ k))
  intro q
  unfold contextHard
  rw [physical_embedding_eq small B s hs σ U hB hσ k e q]
  rfl

end ContingencyTables.SmallContextEnumeration

end OAI
