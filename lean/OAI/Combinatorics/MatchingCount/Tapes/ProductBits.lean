import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.MetropolisChoice

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma product_nonneg {I : Type*} [Fintype I] [DecidableEq I] (p : I → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (x : I → Ω) : 0≤product p x :=
  prod_nonneg (fun i _=>hp i (x i))

lemma product_sum {I : Type*} [Fintype I] [DecidableEq I] (p : I → Ω → ℝ)
    (hp : ∀ i,∑ x,p i x=1) : ∑ x,product p x=1 := by
  unfold product
  rw [←Fintype.prod_sum]
  simp [hp]

lemma product_fin_tv (n : ℕ) (p q : Fin n → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (hps : ∀ i,∑ x,p i x=1)
    (hq : ∀ i x,0≤q i x) (hqs : ∀ i,∑ x,q i x=1) :
    tv (product p) (product q)≤∑ i,tv (p i) (q i) := by
  induction n with
  | zero => simp [tv,product]
  | succ n ih =>
    let e : (Ω×(Fin n → Ω)) ≃ (Fin (n+1) → Ω) := Fin.consEquiv (fun _=>Ω)
    have hpE : product p ∘ e=tensor (p 0) (product (fun i : Fin n=>p i.succ)) := by
      funext x
      simp [product,tensor,e,Fin.prod_univ_succ]
    have hqE : product q ∘ e=tensor (q 0) (product (fun i : Fin n=>q i.succ)) := by
      funext x
      simp [product,tensor,e,Fin.prod_univ_succ]
    rw [←tv_equiv e,hpE,hqE]
    have ht := tensor_tv (p 0) (q 0) (product (fun i : Fin n=>p i.succ))
      (product (fun i : Fin n=>q i.succ)) (hp 0) (hps 0)
      (product_nonneg (fun i : Fin n=>q i.succ) (fun i=>hq i.succ))
      (product_sum (fun i : Fin n=>q i.succ) (fun i=>hqs i.succ))
    rw [Fin.sum_univ_succ]
    exact ht.trans (add_le_add_right (ih _ _ (fun i=>hp i.succ) (fun i=>hps i.succ)
      (fun i=>hq i.succ) (fun i=>hqs i.succ)) _)

lemma product_tv {I : Type*} [Fintype I] [DecidableEq I] (p q : I → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (hps : ∀ i,∑ x,p i x=1)
    (hq : ∀ i x,0≤q i x) (hqs : ∀ i,∑ x,q i x=1) :
    tv (product p) (product q)≤∑ i,tv (p i) (q i) := by
  let e:=Fintype.equivFin I
  let a : (I → Ω) ≃ (Fin (Fintype.card I) → Ω) := Equiv.arrowCongr e (Equiv.refl Ω)
  have he (p : I → Ω → ℝ) : product p ∘ a.symm=product (fun i=>p (e.symm i)) := by
    funext x
    change (∏ i,p i (x (e i)))=∏ j,p (e.symm j) (x j)
    exact Fintype.prod_equiv e _ _ (by simp)
  rw [←tv_equiv a.symm,he,he]
  have ht:=product_fin_tv _ (fun i=>p (e.symm i)) (fun i=>q (e.symm i))
    (fun i=>hp _) (fun i=>hps _) (fun i=>hq _) (fun i=>hqs _)
  rw [e.symm.sum_comp (fun i=>tv (p i) (q i))] at ht
  exact ht

lemma uniform_fun {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (x : I → A) :
    uniform (I → A) x=∏ i,uniform A (x i) := by
  simp [uniform,Nat.cast_pow]

omit [Fintype Ω] in
lemma imageLaw_componentwise [Fintype Ω] {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → Ω) : imageLaw (fun x : I → A=>fun i=>f i (x i))=
      product (fun i=>imageLaw (f i)) := by
  funext y
  let : DecidableEq (I → Ω) := Classical.decEq _
  have he (x : I → A) : (if (fun i=>f i (x i))=y then uniform (I → A) x else 0)=
      ∏ i,if f i (x i)=y i then uniform A (x i) else 0 := by
    by_cases h : (fun i=>f i (x i))=y
    · rw [ite_eq_left h,uniform_fun]
      apply prod_congr rfl
      intro i _
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i,f i (x i)≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  unfold imageLaw push product
  simp_rw [he]
  exact (Fintype.prod_sum (fun i a=>if f i a=y i then uniform A a else 0)).symm

lemma product_restrict {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (p : I → Ω → ℝ) (hs : ∀ i,∑ a,p i a=1) :
    push (product p) (fun x=>fun i : S=>x i.val)=product (fun i : S=>p i.val) := by
  funext y
  let : DecidableEq (S → Ω) := Classical.decEq _
  let q : I → Ω → ℝ := fun i a=>if hi : i∈S then (if a=y ⟨i,hi⟩ then p i a else 0) else p i a
  have he (x : I → Ω) : (if (fun i : S=>x i.val)=y then product p x else 0)=∏ i,q i (x i) := by
    by_cases h : (fun i : S=>x i.val)=y
    · rw [ite_eq_left h]
      apply prod_congr rfl
      intro i _
      by_cases hi : i∈S
      · simp only [q,dite_eq_left hi,congrFun h ⟨i,hi⟩,ite_true]
      · simp only [q,dite_eq_right hi]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i : S,x i.val≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      apply prod_eq_zero (mem_univ i.val)
      simp only [q,dite_eq_left i.property,ite_eq_right hi]
  have hq (i : I) : ∑ a,q i a=if hi : i∈S then p i (y ⟨i,hi⟩) else 1 := by
    by_cases hi : i∈S
    · simp [q,hi]
    · simp [q,hi,hs i]
  unfold push
  simp_rw [he]
  rw [←Fintype.prod_sum]
  simp_rw [hq]
  change (∏ i,if hi : i∈S then p i (y ⟨i,hi⟩) else 1)=∏ i : S,p i.val (y i)
  let g : I → ℝ := fun i=>if hi : i∈S then p i (y ⟨i,hi⟩) else 1
  change (∏ i,g i)=_
  calc
    _ = ∏ i∈S,g i := (prod_subset (subset_univ S) (by intro i _ hi;simp [g,hi])).symm
    _ = ∏ i∈S.attach,g i.val := (Finset.prod_attach S g).symm
    _ = ∏ i : S,p i.val (y i) := by
      rw [Finset.univ_eq_attach]
      apply prod_congr rfl
      intro i _
      simp [g]

lemma imageLaw_tensor {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) :
    imageLaw (fun x : A×B=>(f x.1,g x.2))=tensor (imageLaw f) (imageLaw g) := by
  funext y
  simp only [imageLaw,push,tensor,Fintype.sum_prod_type,uniform_prod,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  by_cases hf : f a=y.1 <;> by_cases hg : g b=y.2 <;> simp [hf,hg,Prod.ext_iff]

lemma push_tensor_sigma {A B : Type*} [Fintype A] [Fintype B] {C : A → Type*}
    [∀ a,Fintype (C a)] (p : A → ℝ) (r : B → ℝ) (f : ∀ a,B → C a) :
    push (tensor p r) (fun x : A×B=>Sigma.mk x.1 (f x.1 x.2))=
      sigmaLift p (fun a=>push r (f a)) := by
  funext x
  obtain ⟨a,c⟩:=x
  simp only [push,tensor,sigmaLift,Fintype.sum_prod_type]
  have he (x : A) : (∑ b,if (⟨x,f x b⟩ : Sigma C)=⟨a,c⟩ then p x*r b else 0)=
      if x=a then p a*(∑ b,if f a b=c then r b else 0) else 0 := by
    by_cases h : x=a
    · subst x
      simp [mul_sum,mul_ite]
    · simp only [ite_eq_right h]
      apply sum_eq_zero
      intro b _
      apply ite_eq_right
      intro he
      exact h (congrArg Sigma.fst he)
  simp_rw [he]
  simp

end MatchingFPRAS.Variation

end OAI
