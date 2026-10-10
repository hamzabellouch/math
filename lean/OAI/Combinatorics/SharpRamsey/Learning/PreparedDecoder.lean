import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestActualRow
import OAI.Combinatorics.SharpRamsey.Learning.GreedyIndexed

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*} [Fintype α]

omit [Fintype α] in

lemma own_inter (S T : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own (S∩T) U bs x=S∩own T U bs x := by
  induction bs generalizing T with
  | nil => simp [own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [own,hx,inter_assoc]
    · simp only [own,ite_eq_right hx]
      rw [show (S∩T)\U b=S∩(T\U b) by ext y; simp only [mem_sdiff,mem_inter]; tauto,ih]

lemma own_public (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x=S∩own univ U bs x := by
  simpa using own_inter S univ U bs x

def sized (S : Finset α) (U : β → Finset α) : List β → List (β×ℕ)
  | [] => []
  | b::bs => (b,(S∩U b).card)::sized (S\U b) U bs

def publicSize (U : β → Finset α) : List (β×ℕ) → α → ℕ
  | [],_ => 0
  | (b,m)::bs,x => if x∈U b then m else publicSize U bs x

omit [Fintype α] in
lemma sized_planes (S : Finset α) (U : β → Finset α) (bs : List β) :
    (sized S U bs).map Prod.fst=bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [sized,ih]

omit [Fintype α] in
lemma publicSize_eq (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    publicSize U (sized S U bs) x=(own S U bs x).card := by
  induction bs generalizing S with
  | nil => simp [sized,publicSize,own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [sized,publicSize,own,hx]
    · simp [sized,publicSize,own,hx,ih]

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedDecoder
open Finset SharpLogRamsey.PreparedRow SharpLogRamsey.PointScore
open SharpLogRamsey.GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {A H B : Type*} [Fintype A] [Fintype H]

def counts (S : Finset A) {R : ℕ} (ω : Schedule S R) : Fin R×A → ℕ :=
  fun rx => extend S ω rx.1 rx.2

def publicSample {R : ℕ} (ω : Fin R×A → ℕ) : Finset A :=
  univ.filter (fun x => ∃ r,ω (r,x)≠0)

def publicScore (own : A → Prop) (T : Finset H) (inc : H → A → Prop)
    (b : ℝ) {R : ℕ} (ω : Fin R×A → ℕ) : ℝ :=
  ∑ h∈T,∏ r,
    (if ∀ y,own y ∧ inc h y → ω (r,y)=0 then (1:ℝ) else 0)*
    ((if ∀ y,¬own y ∧ inc h y → ω (r,y)=0 then (1:ℝ) else 0)-b)

lemma publicSample_eq (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    publicSample (counts S ω)=sample S ω := by
  ext x
  by_cases hx : x∈S
  · constructor
    · intro hh
      exact mem_filter.mpr ⟨hx,(mem_filter.mp hh).2⟩
    · intro hh
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hh).2⟩
  · constructor
    · intro hh
      obtain ⟨r,hr⟩ := (mem_filter.mp hh).2
      exact False.elim (hr (by simp [counts,extend,hx]))
    · intro hh
      exact False.elim (hx (mem_filter.mp hh).1)

omit [Fintype A] in
lemma empty_counts (S : Finset A) (Q : A → Prop) {R : ℕ} (ω : Schedule S R) (r : Fin R) :
    (∀ y,Q y → counts S ω (r,y)=0) ↔ (∀ y : S,Q y.1 → ω (r,y)=0) := by
  constructor
  · intro h y hy
    simpa only [counts,extend,dite_eq_left y.2] using h y.1 hy
  · intro h y hy
    by_cases hs : y∈S
    · simpa only [counts,extend,dite_eq_left hs] using h ⟨y,hs⟩ hy
    · simp [counts,extend,hs]

omit [Fintype H] in
lemma publicScore_eq (S O : Finset A) (Q : A → Prop)
    (hQ : ∀ y∈S,(y∈O ↔ Q y)) (T : Finset H) (inc : H → A → Prop)
    (b : ℝ) {R : ℕ} (ω : Schedule S R) :
    publicScore Q T inc b (counts S ω)=score S O T inc b ω := by
  rw [publicScore,score_eq]
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  simp only [empty_counts,pointEmpty]
  have he₁ : (∀ y : S,Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∈O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  have he₂ : (∀ y : S,¬Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∉O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  simp only [he₁,he₂]
  split_ifs <;> rfl

def decode (U : B → Finset A) (bs : List (B×ℕ)) (N z : ℕ)
    (T : A → Finset H) (inc : H → A → Prop) (L q : ℝ)
    {R : ℕ} (ω : Fin R×A → ℕ) : Finset A :=
  LearningRow.test (publicSample ω)
    (fun x => publicScore (fun y => y∈own univ U (bs.map Prod.fst) x)
      (T x) inc (Real.exp (-L*(1-(publicSize U bs x:ℝ)/(N:ℝ)))) ω) z q

omit [Fintype H] in
theorem decode_equals_source (S₀ S : Finset A) (hS : S⊆S₀)
    (U : B → Finset A) (bs : List B) (T : A → Finset H) (inc : H → A → Prop)
    (L q : ℝ) (z : ℕ) {R : ℕ} (ω : Schedule S R) :
    decode U (sized S₀ U bs) S.card z T inc L q (counts S ω)=
      LearningRow.test (sample S ω)
        (fun x => score S (own S₀ U bs x) (T x) inc
          (Real.exp (-L*(1-((own S₀ U bs x).card:ℝ)/(S.card:ℝ)))) ω) z q := by
  rw [decode,publicSample_eq,sized_planes]
  congr 1
  funext x
  rw [publicSize_eq]
  apply publicScore_eq
  intro y hy
  rw [own_public,mem_inter]
  exact and_iff_right (hS hy)

end
end SharpLogRamsey.PreparedDecoder

end

end OAI
