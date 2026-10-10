import Mathlib

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def used (f : Fin d → Fin (n+1)) : Finset (Fin n) :=
  univ.filter (fun i => ∃ a : Fin d, (f a).val=i.val)

def without (f : Fin d → Fin (n+1)) (i : Fin n) : Fin d → Fin (n+1) :=
  fun a => if (f a).val=i.val then ⟨n,Nat.lt_succ_self n⟩ else f a

theorem used_without (f : Fin d → Fin (n+1)) (i : Fin n) :
    used (without f i)=(used f).erase i := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and,mem_erase]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [without] at ha
    split_ifs at ha with h
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
    · refine ⟨?_,a,ha⟩
      intro he
      exact h (ha.trans (congrArg Fin.val he))
  · rintro ⟨hxi,a,ha⟩
    refine ⟨a,?_⟩
    dsimp only [without]
    rw [ite_eq_right (fun h => hxi (Fin.ext (ha.symm.trans h)))]
    exact ha

def flag (q : Fin n → Bool) (i : Fin n) : ℚ := if q i then 1 else 0

def monomial (q : Fin n → Bool) (f : Fin d → Fin (n+1)) : ℚ :=
  ∏ i ∈ used f, flag q i

def features (q : Fin n → Bool) (j : Fin ((n+1)^d)) : ℚ :=
  monomial q (finFunctionFinEquiv.symm j)

@[simp] theorem features_code (q : Fin n → Bool) (f : Fin d → Fin (n+1)) :
    features q (finFunctionFinEquiv f)=monomial q f := by
  simp only [features,Equiv.symm_apply_apply]

def endpoint (q : Fin n → Bool) (i : Fin n) (b : Fin 2) : Fin n → Bool :=
  fun x => if x=i then decide (b=0) else q x

@[simp] theorem flag_endpoint (q : Fin n → Bool) (i x : Fin n) (b : Fin 2) :
    flag (endpoint q i b) x=if x=i then (if b=0 then 1 else 0) else flag q x := by
  by_cases h : x=i <;> simp [flag,endpoint,h]

theorem monomial_endpoint (q : Fin n → Bool) (f : Fin d → Fin (n+1))
    (i : Fin n) (b : Fin 2) :
    monomial (endpoint q i b) f=
      if i ∈ used f then (if b=0 then 1 else 0)*monomial q (without f i)
      else monomial q f := by
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold monomial
    rw [used_without,← mul_prod_erase (used f) (flag (endpoint q i b)) hi]
    rw [flag_endpoint,ite_eq_left rfl]
    congr 1
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (mem_erase.mp hx).1]
  · rw [ite_eq_right hi]
    unfold monomial
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (fun (he : x=i) => hi (he ▸ hx))]

def target (p : Fin n → ℚ) (t : ℕ) (f : Fin d → Fin (n+1)) : ℚ :=
  ∏ i ∈ used f, if i.val<t then p i else 0

theorem target_succ (p : Fin n → ℚ) (t : ℕ) (ht : t<n) (f : Fin d → Fin (n+1)) :
    target p (t+1) f=
      if (⟨t,ht⟩ : Fin n) ∈ used f then p ⟨t,ht⟩*target p t (without f ⟨t,ht⟩)
      else target p t f := by
  let i : Fin n := ⟨t,ht⟩
  have val_ne : ∀ x : Fin n, x ≠ i → x.val ≠ t := fun x h he => h (Fin.ext he)
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold target
    rw [used_without,← mul_prod_erase (used f) (fun x => if x.val<t+1 then p x else 0) hi]
    simp only [i,show t<t+1 by omega,ite_eq_left]
    congr 1
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (mem_erase.mp hx).1
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]
  · rw [ite_eq_right hi]
    unfold target
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (fun (he : x=i) => hi (he ▸ hx))
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]

end MetricKMedian.SparseBernoulli

end OAI
