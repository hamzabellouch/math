import Mathlib

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- A bounded deterministic computation and the chronological requests it
actually made. Failure retains its prefix and does not query later work. -/
structure Logged (Q α : Type*) where
  result : Option α
  requests : List Q

namespace Logged
variable {Q α β γ : Type*}

def pure (a : α) : Logged Q α := ⟨some a,[]⟩
def abort : Logged Q α := ⟨none,[]⟩
def bind (x : Logged Q α) (f : α→Logged Q β) : Logged Q β :=
  match x.result with
  | none => ⟨none,x.requests⟩
  | some a => ⟨(f a).result,x.requests++(f a).requests⟩
def map (f : α→β) (x : Logged Q α) : Logged Q β := x.bind (fun a => pure (f a))
def Good (P : Q→Prop) (x : Logged Q α) : Prop := ∀ q∈x.requests,P q

lemma good_bind_left (P : Q→Prop) (x : Logged Q α) (f : α→Logged Q β)
    (h : Good P (x.bind f)) : Good P x := by
  intro q hq
  cases hx : x.result with
  | none => exact h q (by simpa only [bind,hx] using hq)
  | some a => exact h q (by simp only [bind,hx,List.mem_append]; exact Or.inl hq)

lemma good_bind_right (P : Q→Prop) (x : Logged Q α) (f : α→Logged Q β) {a : α}
    (hx : x.result=some a) (h : Good P (x.bind f)) : Good P (f a) := by
  intro q hq
  exact h q (by simp only [bind,hx,List.mem_append]; exact Or.inr hq)

lemma bind_result_some (x : Logged Q α) (f : α→Logged Q β) {a : α}
    (hx : x.result=some a) : (x.bind f).result=(f a).result := by simp only [bind,hx]

lemma map_result (f : α→β) (x : Logged Q α) : (x.map f).result=x.result.map f := by
  cases hx : x.result <;> simp [map,bind,hx,pure]

lemma map_requests (f : α→β) (x : Logged Q α) : (x.map f).requests=x.requests := by
  cases hx : x.result <;> simp [map,bind,hx,pure]

lemma good_map (P : Q→Prop) (f : α→β) (x : Logged Q α) :
    Good P (x.map f) ↔ Good P x := by simp only [Good,map_requests]

def traverse (f : α→Logged Q β) : List α→Logged Q (List β)
  | [] => pure []
  | a::as => (f a).bind (fun b => (traverse f as).map (b::·))

/-- No hypothesis at unvisited requests: the induction uses the good prefix,
obtains its successful result, then exposes the actual next prefix. -/
lemma traverse_complete (P : Q→Prop) (f : α→Logged Q β) (g : α→β) (xs : List α)
    (hlocal : ∀ a∈xs, Good P (f a) → (f a).result=some (g a))
    (hg : Good P (traverse f xs)) : (traverse f xs).result=some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have hhead := good_bind_left P _ _ hg
    have hs := hlocal a (by simp) hhead
    have htail := good_bind_right P _ _ hs hg
    have ht := (good_map P (g a::·) (traverse f as)).mp htail
    have hr := ih (fun b hb => hlocal b (by simp [hb])) ht
    rw [traverse,bind_result_some _ _ hs,map_result,hr,Option.map_some,List.map_cons]

lemma traverse_sound (f : α→Logged Q β) (g : α→β) (xs : List α)
    (hlocal : ∀ a∈xs, ∀ b, (f a).result=some b → b=g a)
    {ys : List β} (hs : (traverse f xs).result=some ys) : ys=xs.map g := by
  induction xs generalizing ys with
  | nil => simpa only [traverse,pure,List.map_nil,Option.some.injEq] using hs.symm
  | cons a as ih =>
    cases hf : (f a).result with
    | none => simp only [traverse,bind,hf] at hs; contradiction
    | some b =>
      have hb := hlocal a (by simp) b hf
      rw [traverse,bind_result_some _ _ hf,map_result] at hs
      obtain ⟨bs,hbs,hys⟩ := Option.map_eq_some_iff.mp hs
      have ht := ih (fun c hc => hlocal c (by simp [hc])) hbs
      subst ys
      rw [hb,ht,List.map_cons]

end Logged
end ExactQuantumFactoring


end

end OAI
