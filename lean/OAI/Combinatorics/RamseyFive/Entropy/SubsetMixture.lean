import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Law

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def uniformWeight (S : Finset α) (a : α) : ℝ :=
  if a∈S then 1/(S.card:ℝ) else 0
noncomputable def relationMass (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ) : ℝ :=
  ∑z∈Finset.univ.filter (fun z : α×β=>R z.1 z.2),f z.1*g z.2

omit [Fintype α] in
lemma uniformWeight_nonneg (S : Finset α) (a : α) : 0 ≤ uniformWeight S a := by
  unfold uniformWeight;split_ifs <;> positivity
lemma relationMass_nonneg (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀b,0 ≤ g b) : 0 ≤ relationMass R f g :=
  Finset.sum_nonneg (fun entry _=>mul_nonneg (hf entry.1) (hg entry.2))

lemma relationMass_uniform (R : α→β→Prop) (S : Finset α) (T : Finset β) :
    relationMass R (uniformWeight S) (uniformWeight T)=
      (((S×ˢT).filter (fun z=>R z.1 z.2)).card:ℝ)/((S.card:ℝ)*T.card) := by
  have he : (S×ˢT).filter (fun z=>R z.1 z.2)=
      (Finset.univ.filter (fun z : α×β=>R z.1 z.2)).filter (fun z=>z.1∈S ∧ z.2∈T) := by
    ext z;simp [and_comm]
  rw [he]
  unfold relationMass
  have hterm (z : α×β) :
      uniformWeight S z.1*uniformWeight T z.2=
      if z.1∈S ∧ z.2∈T then 1/((S.card:ℝ)*T.card) else 0 := by
    by_cases hS : z.1∈S <;> by_cases hT : z.2∈T <;> simp [uniformWeight,hS,hT,mul_comm]
  simp_rw [hterm]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  ring

lemma independent_subset_relation (R : α→β→Prop) (μ : Law (Finset α)) (ν : Law (Finset β)) :
    (∑S,∑T,μ S*ν T*relationMass R (uniformWeight S) (uniformWeight T))=
      relationMass R (fun a=>∑S,μ S*uniformWeight S a)
        (fun b=>∑T,ν T*uniformWeight T b) := by
  let E := Finset.univ.filter (fun z : α×β=>R z.1 z.2)
  change (∑S,∑T,μ S*ν T*(∑z∈E,uniformWeight S z.1*uniformWeight T z.2))=
    ∑z∈E,(∑S,μ S*uniformWeight S z.1)*(∑T,ν T*uniformWeight T z.2)
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑S,∑z∈E,∑T,μ S*ν T*(uniformWeight S z.1*uniformWeight T z.2) := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_comm
    _ = ∑z∈E,∑S,∑T,μ S*ν T*(uniformWeight S z.1*uniformWeight T z.2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem independent_subset_domination (R : α→β→Prop)
    (p : Law α) (q : Law β) (μ : Law (Finset α)) (ν : Law (Finset β)) (L : ℝ)
    (hL : 0 ≤ L)
    (hA : ∀a,(∑S,μ S*uniformWeight S a) ≤ L*p a)
    (hB : ∀b,(∑T,ν T*uniformWeight T b) ≤ L*q b) :
    (∑S,∑T,μ S*ν T*relationMass R (uniformWeight S) (uniformWeight T)) ≤
      L^2*relationMass R p q := by
  rw [independent_subset_relation]
  unfold relationMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hn : 0 ≤ ∑T,ν T*uniformWeight T z.2 := Finset.sum_nonneg
    (fun T _=>mul_nonneg (ν.nonneg T) (uniformWeight_nonneg T z.2))
  have hh := mul_le_mul (hA z.1) (hB z.2) hn (mul_nonneg hL (p.nonneg z.1))
  nlinarith only [hh]

lemma independent_law_lower (μ : Law α) (ν : Law β) (f : α→β→ℝ) (c : ℝ)
    (h : ∀a b,0 < μ a→0 < ν b→c ≤ f a b) :
    c ≤ ∑a,∑b,μ a*ν b*f a b := by
  have hp (a : α) (b : β) : μ a*ν b*c ≤ μ a*ν b*f a b := by
    by_cases ha : μ a=0
    · simp [ha]
    by_cases hb : ν b=0
    · simp [hb]
    exact mul_le_mul_of_nonneg_left (h a b (lt_of_le_of_ne (μ.nonneg a) (Ne.symm ha))
      (lt_of_le_of_ne (ν.nonneg b) (Ne.symm hb))) (mul_nonneg (μ.nonneg a) (ν.nonneg b))
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun b _=>hp a b))
  simpa only [←Finset.sum_mul,←Finset.mul_sum,ν.sum_one,μ.sum_one,mul_one,one_mul] using hs

end

open scoped BigOperators Classical
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]

lemma relationMass_by_target (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ) :
    relationMass R f g=∑b,g b*(∑a∈Finset.univ.filter (fun a=>R a b),f a) := by
  unfold relationMass
  rw [Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

omit [Fintype α] in
lemma sum_uniformWeight (X H : Finset α) :
    (∑a∈H,uniformWeight X a)=((H∩X).card:ℝ)/X.card := by
  unfold uniformWeight
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he : H.filter (fun a=>a∈X)=H∩X := by ext a;simp
  rw [he]
  ring

lemma relationMass_neighbors (R : α→β→Prop) (X : Finset α) (Y : Finset β) :
    relationMass R (uniformWeight X) (uniformWeight Y)=
      ∑b,uniformWeight Y b*((((Finset.univ.filter (fun a=>R a b))∩X).card:ℝ)/X.card) := by
  rw [relationMass_by_target]
  simp_rw [sum_uniformWeight]

lemma independent_support_relation (R : α→β→Prop) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset α) (Y : κ→Finset β) :
    (∑i,∑j,μ i*ν j*relationMass R (uniformWeight (X i)) (uniformWeight (Y j)))=
      relationMass R (fun a=>∑i,μ i*uniformWeight (X i) a)
        (fun b=>∑j,ν j*uniformWeight (Y j) b) := by
  let E := Finset.univ.filter (fun z : α×β=>R z.1 z.2)
  change (∑i,∑j,μ i*ν j*(∑z∈E,uniformWeight (X i) z.1*uniformWeight (Y j) z.2))=
    ∑z∈E,(∑i,μ i*uniformWeight (X i) z.1)*(∑j,ν j*uniformWeight (Y j) z.2)
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑i,∑z∈E,∑j,μ i*ν j*(uniformWeight (X i) z.1*uniformWeight (Y j) z.2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑z∈E,∑i,∑j,μ i*ν j*(uniformWeight (X i) z.1*uniformWeight (Y j) z.2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma independent_support_domination (R : α→β→Prop) (p : Law α) (r : Law β)
    (μ : Law ι) (ν : Law κ) (X : ι→Finset α) (Y : κ→Finset β) (L : ℝ)
    (hL : 0 ≤ L) (hX : ∀a,(∑i,μ i*uniformWeight (X i) a) ≤ L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b) ≤ L*r b) :
    (∑i,∑j,μ i*ν j*relationMass R (uniformWeight (X i)) (uniformWeight (Y j))) ≤
      L^2*relationMass R p r := by
  rw [independent_support_relation]
  unfold relationMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hn : 0 ≤ ∑j,ν j*uniformWeight (Y j) z.2 := Finset.sum_nonneg
    (fun j _=>mul_nonneg (ν.nonneg j) (uniformWeight_nonneg _ _))
  have hh := mul_le_mul (hX z.1) (hY z.2) hn (mul_nonneg hL (p.nonneg z.1))
  nlinarith only [hh]

theorem adaptive_rejection_average {Θ : Type*} [Fintype Θ]
    (R : α→β→Prop) (p : Law α) (r : Law β)
    (μ : Law ι) (ν : Law κ) (X : ι→Finset α) (Y : κ→Finset β)
    (prior : ι→κ→Law Θ) (reject : ι→κ→Θ→β→ℝ) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a) ≤ L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b) ≤ L*r b)
    (hlocal : ∀i j θ b,reject i j θ b ≤
      B*((((Finset.univ.filter (fun a=>R a b))∩X i).card:ℝ)/(X i).card)) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑b,uniformWeight (Y j) b*reject i j θ b))) ≤
      B*L^2*relationMass R p r := by
  have hpoint (i : ι) (j : κ) :
      (∑θ,prior i j θ*(∑b,uniformWeight (Y j) b*reject i j θ b)) ≤
        B*relationMass R (uniformWeight (X i)) (uniformWeight (Y j)) := by
    have ht (θ : Θ) : (∑b,uniformWeight (Y j) b*reject i j θ b) ≤
        B*relationMass R (uniformWeight (X i)) (uniformWeight (Y j)) := by
      rw [relationMass_neighbors,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b _
      have hh := mul_le_mul_of_nonneg_left (hlocal i j θ b) (uniformWeight_nonneg (Y j) b)
      nlinarith only [hh]
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun θ _=>
      mul_le_mul_of_nonneg_left (ht θ) ((prior i j).nonneg θ))
    simpa only [←Finset.sum_mul,(prior i j).sum_one,one_mul] using hs
  calc
    _ ≤ ∑i,∑j,μ i*ν j*(B*relationMass R (uniformWeight (X i)) (uniformWeight (Y j))) :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>
        mul_le_mul_of_nonneg_left (hpoint i j) (mul_nonneg (μ.nonneg i) (ν.nonneg j))))
    _ = B*(∑i,∑j,μ i*ν j*relationMass R (uniformWeight (X i)) (uniformWeight (Y j))) := by
      simp_rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro j _;ring
    _ ≤ B*(L^2*relationMass R p r) := mul_le_mul_of_nonneg_left
      (independent_support_domination R p r μ ν X Y L hL hX hY) hB
    _ = _ := by ring

end SharpRamseyFive.FiniteEntropy

end OAI
