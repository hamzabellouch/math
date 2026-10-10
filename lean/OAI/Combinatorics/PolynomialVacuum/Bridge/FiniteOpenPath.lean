import Mathlib

namespace OAI

namespace PolynomialVacuumOpenPath
open Classical
variable {α : Type*}

def follow (f : α → Option α) (a : α) : ℕ → Option α
  | 0 => some a
  | n+1 => (follow f a n).bind f

@[simp] theorem follow_zero (f : α → Option α) (a : α) : follow f a 0=some a := rfl
@[simp] theorem follow_succ (f : α → Option α) (a : α) (n : ℕ) :
    follow f a (n+1)=(follow f a n).bind f := rfl

 
theorem follow_injective (f : α → Option α)
    (hf : ∀ u v w,f u=some w → f v=some w → u=v) (a : α)
    (ha : ∀ u,f u≠some a) {i j : ℕ} {b : α}
    (hi : follow f a i=some b) (hj : follow f a j=some b) : i=j := by
  induction i generalizing j b with
  | zero =>
    have hb : a=b := Option.some.inj hi
    subst b
    cases j with
    | zero => rfl
    | succ j =>
      rw [follow_succ] at hj
      cases hh : follow f a j with
      | none => simp [hh] at hj
      | some u => exact (ha u (by simpa [hh] using hj)).elim
  | succ i ih =>
    cases j with
    | zero =>
      have hb : a=b := Option.some.inj hj
      subst b
      rw [follow_succ] at hi
      cases hh : follow f a i with
      | none => simp [hh] at hi
      | some u => exact (ha u (by simpa [hh] using hi)).elim
    | succ j =>
      rw [follow_succ] at hi hj
      cases hu : follow f a i with
      | none => simp [hu] at hi
      | some u =>
        cases hv : follow f a j with
        | none => simp [hv] at hj
        | some v =>
          have he : u=v := hf u v b (by simpa [hu] using hi) (by simpa [hv] using hj)
          subst v
          exact congrArg Nat.succ (ih hu hv)

theorem eventually_exits [Fintype α] (f : α → Option α)
    (hf : ∀ u v w,f u=some w → f v=some w → u=v) (a : α)
    (ha : ∀ u,f u≠some a) : ∃ n,follow f a n=none := by
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ b,follow f a n=some b := Option.ne_none_iff_exists'.mp (hn n)
  let g : Fin (Fintype.card α+1) → α:=fun n => (hex n.val).choose
  have hg : Function.Injective g := by
    intro i j he
    apply Fin.ext
    apply follow_injective f hf a ha ((hex i.val).choose_spec)
    change (hex i.val).choose=(hex j.val).choose at he
    rw [he]
    exact (hex j.val).choose_spec
  have hc:=Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hc
  omega

section Exit
variable [Fintype α] (f : α → Option α)
    (hf : ∀ u v w,f u=some w → f v=some w → u=v) (a : α)
    (ha : ∀ u,f u≠some a)
noncomputable def exitTime : ℕ := Nat.find (eventually_exits f hf a ha)

theorem exitTime_spec : follow f a (exitTime f hf a ha)=none :=
  Nat.find_spec (eventually_exits f hf a ha)

theorem exitTime_pos : 0<exitTime f hf a ha := by
  have h:=exitTime_spec f hf a ha
  by_contra hn
  have hz : exitTime f hf a ha=0 := by omega
  simp [hz] at h

theorem beforeExit_some (j : Fin (exitTime f hf a ha)) : ∃ b,follow f a j.val=some b := by
  apply Option.ne_none_iff_exists'.mp
  exact Nat.find_min (eventually_exits f hf a ha) j.isLt

noncomputable def pathAt (j : Fin (exitTime f hf a ha)) : α :=
  (beforeExit_some f hf a ha j).choose

theorem pathAt_spec (j : Fin (exitTime f hf a ha)) :
    follow f a j.val=some (pathAt f hf a ha j) :=
  (beforeExit_some f hf a ha j).choose_spec

theorem pathAt_injective : Function.Injective (pathAt f hf a ha) := by
  intro i j hij
  apply Fin.ext
  apply follow_injective f hf a ha (pathAt_spec f hf a ha i)
  rw [hij]
  exact pathAt_spec f hf a ha j

theorem pathAt_start : pathAt f hf a ha ⟨0,exitTime_pos f hf a ha⟩=a := by
  exact (Option.some.inj (pathAt_spec f hf a ha ⟨0,exitTime_pos f hf a ha⟩)).symm

theorem pathAt_next (i j : Fin (exitTime f hf a ha)) (hij : j.val=i.val+1) :
    f (pathAt f hf a ha i)=some (pathAt f hf a ha j) := by
  have h:=pathAt_spec f hf a ha j
  rw [hij,follow_succ,pathAt_spec] at h
  exact h

theorem pathAt_exit (i : Fin (exitTime f hf a ha)) (hi : i.val+1=exitTime f hf a ha) :
    f (pathAt f hf a ha i)=none := by
  have h:=exitTime_spec f hf a ha
  rw [← hi,follow_succ,pathAt_spec] at h
  exact h
end Exit

end PolynomialVacuumOpenPath

end OAI
