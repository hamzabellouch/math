import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

abbrev Star (I T : Type) := I ⊕ ((T × T) ⊕ T)

def outside (P : T → Finset I) : Finset I := univ.filter (fun i => ∀ t, i ∉ P t)

def targets (A : T → Finset I) : Star I T → Finset T
  | .inl i => univ.filter (fun t => i ∈ A t)
  | .inr (.inl st) => {st.1}
  | .inr (.inr t) => {t}

def flag : Star I T → ℝ
  | .inl _ => 1
  | .inr _ => 0

noncomputable def weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ) : Star I T → ℝ
  | .inl i => if i ∈ outside P then y i else 0
  | .inr (.inl st) => ∑ i ∈ A st.1 ∩ P st.2, y i
  | .inr (.inr t) => γ*c t

omit [DecidableEq T] in

theorem mass_partition (y : I → ℝ) (P : T → Finset I)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t))) (F : Finset I) :
    (∑ i ∈ F ∩ outside P, y i)+(∑ t, ∑ i ∈ F ∩ P t, y i)=∑ i ∈ F, y i := by
  simp_rw [← sum_ite_mem]
  rw [sum_comm,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : ∃ t, i ∈ P t
  · obtain ⟨t,ht⟩ := hi
    have hu : i ∉ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun h => h t ht
    rw [ite_eq_right hu,sum_eq_single t,ite_eq_left ht,zero_add]
    · intro s _ hst
      exact ite_eq_right (fun hs => (disjoint_left.mp (hP hst)) hs ht)
    · simp
  · have hu : i ∈ outside P := by simp only [outside,mem_filter,mem_univ,true_and]; exact fun t ht => hi ⟨t,ht⟩
    have hn : ∀ t, i ∉ P t := fun t ht => hi ⟨t,ht⟩
    simp only [ite_eq_left hu,hn,ite_false,sum_const_zero,add_zero]

theorem targeted_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t) (t : T) :
    (∑ e, if t ∈ targets A e then weight y P A c γ e else 0)=(1+γ)*c t := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [targets,weight,mem_filter,mem_univ,true_and,mem_singleton]
  have ho : (∑ i, if i ∈ A t then (if i ∈ outside P then y i else 0) else 0)=
      ∑ i ∈ A t ∩ outside P, y i := by
    rw [sum_ite_mem,univ_inter,sum_ite_mem]
  have hb : (∑ s, ∑ r, if t=s then ∑ i ∈ A s ∩ P r, y i else 0)=
      ∑ r, ∑ i ∈ A t ∩ P r, y i := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true]
  rw [ho,hb,sum_ite_eq,ite_eq_left (mem_univ t)]
  have hp := mass_partition y P hP (A t)
  rw [hc t] at hp
  linarith only [hp]

omit [DecidableEq T] in
 theorem flagged_weight (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ) :
    (∑ e, flag e*weight y P A c γ e)=∑ i ∈ outside P, y i := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [flag,weight,one_mul,zero_mul,sum_const_zero,add_zero,sum_ite_mem,univ_inter]

 theorem target_card_sum {E : Type} [Fintype E] (D : E → Finset T) (w : E → ℝ) :
    (∑ e, ((D e).card:ℝ)*w e)=∑ t, ∑ e, if t ∈ D e then w e else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]

theorem raw_identity (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hunit : ∀ t, (∑ i ∈ P t, y i)+c t=1) :
    (Fintype.card T:ℝ)+(∑ e, (flag e-((targets A e).card:ℝ))*weight y P A c γ e)=
      (∑ i, y i)-γ*∑ t, c t := by
  simp_rw [sub_mul]
  rw [sum_sub_distrib,flagged_weight,target_card_sum]
  simp_rw [targeted_weight y P A c γ hP hc]
  rw [← mul_sum]
  have hp := mass_partition y P hP univ
  simp only [univ_inter] at hp
  have hu := congrArg (fun f : T → ℝ => ∑ t, f t) (funext hunit)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,card_univ] at hu
  linarith only [hu,hp]

omit [DecidableEq T] in
 theorem weight_nonneg (y : I → ℝ) (P A : T → Finset I) (c : T → ℝ) (γ : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hc : ∀ t, 0 ≤ c t) (hγ : 0 ≤ γ) :
    ∀ e, 0 ≤ weight y P A c γ e := by
  rintro (i | (st | t))
  · dsimp only [weight]; split_ifs; exact hy i; exact le_rfl
  · exact sum_nonneg (fun i _ => hy i)
  · exact mul_nonneg hγ (hc t)

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
