import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Best

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

def Captured (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (k : ℕ) (hk : 0<k) : Prop :=
  X.card≤2*(X.card-(remaining F hF shape X (stopIndex F hF shape X k hk)).card)

noncomputable def peelSet (enabled : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) : Finset A :=
  if enabled then retained F hF shape X k hk else X

noncomputable def peelLength (enabled : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) : ℕ :=
  if enabled ∧ Captured F hF shape X k hk then stopIndex F hF shape X k hk else 0

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

lemma peel_half (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    X.card≤2*(peelSet e F hF shape X k hk).card := by
  unfold peelSet
  split_ifs
  · exact retained_half F hF shape X k hk
  · omega

lemma peel_length_bound (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelLength e F hF shape X k hk*k≤X.card := by
  unfold peelLength
  split_ifs
  · exact list_length_bound F hF shape X k hk
  · simp

lemma peel_alternative (e : Prop) (he : e) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk = X\remaining F hF shape X (peelLength e F hF shape X k hk) ∨
    (peelLength e F hF shape X k hk=0 ∧ ∀i∈F,(peelSet e F hF shape X k hk∩shape i).card<k) := by
  by_cases hc : Captured F hF shape X k hk
  · left
    simp only [peelSet,ite_eq_left he,peelLength,ite_eq_left (And.intro he hc)]
    exact ite_eq_left hc
  · right
    refine ⟨by simp [peelLength,hc],?_⟩
    intro i hi
    simpa only [peelSet,ite_eq_left he] using residual_cap F hF shape X k hk hc i hi

lemma cell_subset_captured (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) {j J : ℕ} (hj : j<J) :
    cell F hF shape X j⊆X\remaining F hF shape X J := by
  rw [captured_eq_biUnion_cells]
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,hx⟩

lemma ownCell_zero (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (x : A) : ownCell F hF shape X 0 x=∅ := by
  simp [ownCell]

lemma peel_own_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) (x : A) :
    ownCell F hF shape X (peelLength e F hF shape X k hk) x⊆peelSet e F hF shape X k hk := by
  by_cases hc : e ∧ Captured F hF shape X k hk
  · have hc' : X.card≤2*(X.card-(remaining F hF shape X (stopIndex F hF shape X k hk)).card) := hc.2
    simp only [peelLength,ite_eq_left hc,peelSet,ite_eq_left hc.1,retained,ite_eq_left hc']
    unfold ownCell
    split_ifs with hx
    · exact cell_subset_captured F hF shape X hx
    · exact Finset.empty_subset _
  · simp only [peelLength,ite_eq_right hc,ownCell_zero]
    exact Finset.empty_subset _

lemma two_peels_quarter (e₁ e₂ : Prop) (F₁ F₂ : Finset I) (hF₁ : F₁.Nonempty)
    (hF₂ : F₂.Nonempty) (shape₁ shape₂ : I→Finset A) (X : Finset A)
    (k₁ k₂ : ℕ) (hk₁ : 0<k₁) (hk₂ : 0<k₂) :
    X.card≤4*(peelSet e₂ F₂ hF₂ shape₂ (peelSet e₁ F₁ hF₁ shape₁ X k₁ hk₁) k₂ hk₂).card := by
  have h₁ := peel_half e₁ F₁ hF₁ shape₁ X k₁ hk₁
  have h₂ := peel_half e₂ F₂ hF₂ shape₂ (peelSet e₁ F₁ hF₁ shape₁ X k₁ hk₁) k₂ hk₂
  omega

lemma peel_length_real (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (t : ℝ) (ht : 0<t) :
    (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*t≤X.card := by
  have hi := peel_length_bound e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  calc
    _ ≤ (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*⌈t⌉₊ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil t) (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast hi

lemma peel_residual_real (e : Prop) (he : e) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (t : ℝ) (ht : 0<t) :
    peelSet e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht) =
        X\remaining F hF shape X (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)) ∨
    (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)=0 ∧ ∀i∈F,
      ((peelSet e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)∩shape i).card:ℝ)<t) := by
  rcases peel_alternative e he F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht) with h|⟨hJ,hh⟩
  · exact Or.inl h
  · exact Or.inr ⟨hJ,fun i hi => Nat.lt_ceil.mp (hh i hi)⟩

noncomputable def clippedPart (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) : Option (Fin J)→Finset A
  | none => ∅
  | some i => S∩cell F hF shape X i

noncomputable def queryPart (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) : Option (Fin J) :=
  if h : firstAt F hF shape X J x<J then some ⟨firstAt F hF shape X J x,h⟩ else none

lemma clippedPart_subset (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (i : Option (Fin J)) :
    clippedPart S F hF shape X J i⊆S := by
  cases i
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

lemma clippedPart_disjoint (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) :
    Pairwise (fun i j => Disjoint (clippedPart S F hF shape X J i) (clippedPart S F hF shape X J j)) := by
  intro i j hij
  cases i with
  | none => simp [clippedPart]
  | some i =>
    cases j with
    | none => simp [clippedPart]
    | some j =>
      have hneq : i≠j := by simpa only [ne_eq,Option.some.injEq] using hij
      have hv : i.val≠j.val := fun hh => hneq (Fin.ext hh)
      rcases lt_or_gt_of_ne hv with h|h
      · exact (cell_disjoint_of_lt F hF shape X h).mono Finset.inter_subset_right Finset.inter_subset_right
      · exact (cell_disjoint_of_lt F hF shape X h).symm.mono Finset.inter_subset_right Finset.inter_subset_right

lemma clippedPart_query (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    clippedPart S F hF shape X J (queryPart F hF shape X J x)=S∩ownCell F hF shape X J x := by
  unfold queryPart ownCell
  split_ifs with h
  · rfl
  · simp [clippedPart]

end SharpRamseyFive.GreedyTraining

namespace SharpRamseyFive.TrainingCells
open scoped BigOperators Classical
variable {A H P : Type*} [DecidableEq A] [Fintype H] [Fintype P]

noncomputable def family (C : H→Finset A) (D : P→Finset A) : H⊕P⊕(H×P)→Finset A
  | Sum.inl i => C i
  | Sum.inr (Sum.inl j) => D j
  | Sum.inr (Sum.inr ij) => C ij.1∩D ij.2

lemma sum_card_le (S : Finset A) {J : Type*} [Fintype J] (C : J→Finset A)
    (hsub : ∀j,C j⊆S) (hdis : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (∑j,(C j).card)≤S.card := by
  have hpair : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint C :=
    fun i _ j _ hij => hdis hij
  rw [←Finset.card_biUnion hpair]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => hsub j)

omit [Fintype H] [Fintype P] in
lemma inter_disjoint (C : H→Finset A) (D : P→Finset A)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) (hD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    Pairwise (fun ij kl : H×P => Disjoint (C ij.1∩D ij.2) (C kl.1∩D kl.2)) := by
  intro ij kl hne
  by_cases hi : ij.1=kl.1
  · have hj : ij.2≠kl.2 := fun hh => hne (Prod.ext hi hh)
    exact (hD hj).mono Finset.inter_subset_right Finset.inter_subset_right
  · exact (hC hi).mono Finset.inter_subset_left Finset.inter_subset_left

lemma family_mass (S : Finset A) (C : H→Finset A) (D : P→Finset A)
    (hC : ∀i,C i⊆S) (hD : ∀j,D j⊆S)
    (hdC : Pairwise (fun i j => Disjoint (C i) (C j))) (hdD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    (∑i,(family C D i).card)≤3*S.card := by
  have h₁ := sum_card_le S C hC hdC
  have h₂ := sum_card_le S D hD hdD
  have h₃ := sum_card_le S (fun ij : H×P => C ij.1∩D ij.2)
    (fun ij => Finset.inter_subset_left.trans (hC ij.1)) (inter_disjoint C D hdC hdD)
  simp only [Fintype.sum_sum_type,family]
  omega

omit [Fintype H] [Fintype P] in
lemma family_subsets (S : Finset A) (C : H→Finset A) (D : P→Finset A)
    (hC : ∀i,C i⊆S) (hD : ∀j,D j⊆S) (i : H⊕P⊕(H×P)) : family C D i⊆S := by
  rcases i with i | j | ij
  · exact hC i
  · exact hD j
  · exact Finset.inter_subset_left.trans (hC ij.1)

lemma small_union (S : Finset A) (C D : Finset A) (hS : S.Nonempty)
    (hC : (C.card:ℝ)≤(S.card:ℝ)/25) (hD : (D.card:ℝ)≤(S.card:ℝ)/25) :
    ((C∪D).card:ℝ)/(S.card:ℝ)≤2/25 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hS.card_pos)).mpr
  have hc : ((C∪D).card:ℝ)≤(C.card:ℝ)+D.card := by exact_mod_cast Finset.card_union_le C D
  linarith only [hc,hC,hD]

end SharpRamseyFive.TrainingCells

end OAI
