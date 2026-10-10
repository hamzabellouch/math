import OAI.Computability.MatchingCount.SumRoutine

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma bounded_stops {α : Type} (f : α → α) (active : α → Bool) (rank : α → ℕ)
    (hfix : ∀ a,active a=false → f a=a)
    (hdec : ∀ a,active a=true → rank (f a)+1≤rank a) :
    ∀ n a,rank a≤n → active (f^[n] a)=false := by
  intro n
  induction n with
  | zero =>
    intro a ha
    cases h : active a with
    | false => simpa using h
    | true => have hh := hdec a h; omega
  | succ n ih =>
    intro a ha
    cases h : active a with
    | false => rw [Function.iterate_fixed (hfix a h)]; exact h
    | true =>
      rw [Function.iterate_succ_apply]
      apply ih
      have hh := hdec a h
      omega

def divActive (z : ℕ×(ℕ×ℕ)) : Bool := decide (0<z.1) && decide (z.1≤z.2.1)
def divStep (z : ℕ×(ℕ×ℕ)) : ℕ×(ℕ×ℕ) :=
  if divActive z then (z.1,(z.2.1-z.1,z.2.2+1)) else z

lemma divStep_spec (z : ℕ×(ℕ×ℕ)) :
    (divStep z).1=z.1 ∧ (divStep z).2.1≤z.2.1 ∧ (divStep z).2.2≤z.2.2+1 ∧
      (divStep z).2.1+z.1*(divStep z).2.2=z.2.1+z.1*z.2.2 := by
  unfold divStep
  split_ifs with h
  · have hz : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using h
    have he := Nat.sub_add_cancel hz.2
    dsimp only
    refine ⟨rfl,Nat.sub_le _ _,le_rfl,?_⟩
    nlinarith
  · simp

lemma divIterate_spec (n : ℕ) (z : ℕ×(ℕ×ℕ)) :
    (divStep^[n] z).1=z.1 ∧ (divStep^[n] z).2.1≤z.2.1 ∧ (divStep^[n] z).2.2≤z.2.2+n ∧
      (divStep^[n] z).2.1+z.1*(divStep^[n] z).2.2=z.2.1+z.1*z.2.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h₁,h₂,h₃,h₄⟩ := divStep_spec (divStep^[n] z)
    rw [ih.1] at h₁ h₄
    exact ⟨h₁,h₂.trans ih.2.1,by omega,h₄.trans ih.2.2.2⟩

lemma divIterate_stops (n m : ℕ) : divActive (divStep^[n] (m,n,0))=false := by
  apply bounded_stops divStep divActive (fun z => z.2.1)
    (fun z hz => by simp [divStep,hz]) (fun z hz => ?_) n (m,n,0) le_rfl
  have hh : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using hz
  simp only [divStep,hz,ite_true]
  omega

lemma divIterate_result (n m : ℕ) : (divStep^[n] (m,n,0)).2=(n%m,n/m) := by
  obtain ⟨hm,_,_,hh⟩ := divIterate_spec n (m,n,0)
  have hs := divIterate_stops n m
  by_cases hm0 : m=0
  · subst m
    have hf : divStep (0,n,0)=(0,n,0) := by simp [divStep,divActive]
    rw [Function.iterate_fixed hf]
    simp
  · have hr : (divStep^[n] (m,n,0) ).2.1 < m := by
      have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      simpa [divActive,hm,hpos] using hs
    simp only [Nat.mul_zero,Nat.add_zero] at hh
    have hq : n/m=(divStep^[n] (m,n,0)).2.2 := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    apply Prod.ext
    · have hn := Nat.mod_add_div n m
      rw [hq] at hn
      omega
    · exact hq.symm

namespace Poly
@[fun_prop] theorem natDivMod : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2)) := by
  have hs : Poly divStep := by unfold divStep divActive; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×(ℕ×ℕ)) => divStep^[z.1] z.2) :=
    boundedIterate divStep hs X (by
      intro z j hj
      obtain ⟨h₁,h₂,h₃,_⟩ := divIterate_spec j z.2
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_X,h₁]
      omega)
  have hh : Poly (fun z : ℕ×ℕ => (divStep^[z.1] (z.2,z.1,0)).2) := by fun_prop
  exact hh.congr (fun z => divIterate_result z.1 z.2)

@[fun_prop] theorem natDiv : Poly (fun z : ℕ×ℕ => z.1/z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).2) := second _ natDivMod
  exact h
@[fun_prop] theorem natMod : Poly (fun z : ℕ×ℕ => z.1%z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).1) := first _ natDivMod
  exact h
end Poly
end BinaryMatching.StackCode
end

end OAI
