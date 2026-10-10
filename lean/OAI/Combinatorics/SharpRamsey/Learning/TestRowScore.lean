import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestLearningRowBase
import OAI.Combinatorics.SharpRamsey.Learning.TestLearningIncidence

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PointScore
open scoped BigOperators Classical
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

abbrev Schedule (S : Finset A) (R : ℕ) := Fin R × S → ℕ

def extend (S : Finset A) {R : ℕ} (ω : Schedule S R) (r : Fin R) (x : A) : ℕ :=
  if hx : x∈S then ω (r,⟨x,hx⟩) else 0

def sample (S : Finset A) {R : ℕ} (ω : Schedule S R) : Finset A :=
  S.filter (fun x => ∃ r,extend S ω r x≠0)

def empty (S : Finset A) {R : ℕ} (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) : Prop := ∀ r (y : S),inc h y → ω (r,y)=0

def emptySet (S : Finset A) (E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (ω : Schedule S R) : Finset H := E.filter (empty S inc ω)

def score (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) : ℝ :=
  pointScore (fun y : S => y.1∈O) (fun (h : T) (y : S) => inc h.1 y.1) b ω

omit [Fintype A] [Fintype H] in
lemma unsampled (S : Finset A) {R : ℕ} (ω : Schedule S R) (x : A)
    (hx : x∉sample S ω) : ∀ r (y : S),y.1=x → ω (r,y)=0 := by
  intro r y hy
  subst x
  have hn : ¬∃ r,extend S ω r y.1≠0 := fun h => hx (mem_filter.mpr ⟨y.2,h⟩)
  have hh : extend S ω r y.1=0 := Classical.not_not.mp (fun h => hn ⟨r,h⟩)
  simpa only [extend,dite_eq_left y.2] using hh

omit [Fintype A] [Fintype H] in
lemma sample_subset (S : Finset A) {R : ℕ} (ω : Schedule S R) : sample S ω⊆S := filter_subset _ _

omit [Fintype A] [Fintype H] in
lemma score_eq (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T, ∏ r,
      pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
        (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b) := by
  exact sum_coe_sort T (fun h : H => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b))

omit [Fintype A] [Fintype H] in
lemma score_partition (S O : Finset A) (T E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = score S O (T\E) inc b ω+score S O (T∩E) inc b ω := by
  simp only [score_eq]
  have hh := (sum_sdiff (inter_subset_left (s₁:=T) (s₂:=E)) (f:=fun h => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b)))
  have he : T \ (T∩E)=T\E := by ext h; simp only [mem_sdiff,mem_inter]; tauto
  simpa only [he] using hh.symm

omit [Fintype A] [Fintype H] in
lemma empty_iff (S : Finset A) {R : ℕ} (inc : H → A → Prop)
    (ω : Schedule S R) (h : H) :
    empty S inc ω h ↔ SharpLogRamsey.ExceptionalScore.fullyEmpty
      (univ.filter (fun y : S => inc h y.1)) (fun r y => ω (r,y)) := by
  simp only [empty,ExceptionalScore.fullyEmpty,ExceptionalScore.empty,mem_filter,mem_univ,true_and]

omit [Fintype A] [Fintype H] in

lemma score_exceptional_term (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T,ExceptionalScore.term
      (univ.filter (fun y : S => y.1∈O ∧ inc h y.1))
      (univ.filter (fun y : S => y.1∉O ∧ inc h y.1)) b (fun r y => ω (r,y)) := by
  rw [score_eq]
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  simp only [pointEmpty,ExceptionalScore.empty,mem_filter,mem_univ,true_and]
  split_ifs <;> simp_all

omit [Fintype A] [Fintype H] in
lemma own_outside_union (S O : Finset A) (inc : H → A → Prop) (h : H) :
    (univ.filter (fun y : S => y.1∈O ∧ inc h y.1)) ∪
      (univ.filter (fun y : S => y.1∉O ∧ inc h y.1)) =
      univ.filter (fun y : S => inc h y.1) := by
  ext y
  simp only [mem_union,mem_filter,mem_univ,true_and]
  tauto

omit [Fintype A] [Fintype H] in

theorem exceptional_error (S O : Finset A) (T E : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) (hb : 0≤b) (hb1 : b≤1) :
    |(score S O T inc b ω-score S O (T\E) inc b ω)-
      (1-b)^R*((T∩emptySet S E inc ω).card:ℝ)|≤b*((T∩E).card:ℝ) := by
  classical
  have hp := score_partition S O T E inc b ω
  have hcard : (T∩emptySet S E inc ω)=(T∩E).filter (empty S inc ω) := by
    ext h
    simp only [emptySet,mem_inter,mem_filter]
    tauto
  have hh := ExceptionalScore.exceptional_error (T∩E)
    (fun h => univ.filter (fun y : S => inc h y.1))
    (fun h => univ.filter (fun y : S => y.1∈O ∧ inc h y.1))
    (fun h => univ.filter (fun y : S => y.1∉O ∧ inc h y.1)) b (fun r y => ω (r,y)) hb hb1 (by
      intro h _
      simp only [ExceptionalScore.fullyEmpty,ExceptionalScore.empty,mem_union,
        mem_filter,mem_univ,true_and]
      constructor
      · intro he r y hy
        exact he r y (hy.elim And.right And.right)
      · intro he r y hy
        by_cases ho : y.1∈O
        · exact he r y (Or.inl ⟨ho,hy⟩)
        · exact he r y (Or.inr ⟨ho,hy⟩))
  rw [←score_exceptional_term S O (T∩E) inc b ω] at hh
  simp only [Fintype.card_fin,←empty_iff] at hh
  rw [hp,add_sub_cancel_left,hcard]
  exact hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
