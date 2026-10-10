import OAI.Computability.MatchingCount.RecursiveCoding

namespace OAI

section

namespace BinaryMatching.RecursiveEval
open StackCode
variable {A B C : Type}

def CommandGood (K : ℕ) (PA : A → Prop) (PC : C → Prop) : Command A C → Prop
  | .call k a => k≤K ∧ PA a
  | .join c => PC c

def StateGood (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop) (s : State A B C) : Prop :=
  (∀ c∈s.1,CommandGood K PA PC c) ∧ (∀ b∈s.2,PB b)

lemma step_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) :
    StateGood K PA PB PC (step zero expand combine s) := by
  rcases s with ⟨w,v⟩
  rcases hs with ⟨hw,hv⟩
  cases w with
  | nil => exact ⟨hw,hv⟩
  | cons cmd w =>
    have hw' : ∀ c∈w,CommandGood K PA PC c := fun c h => hw c (List.mem_cons_of_mem _ h)
    have hcmd := hw cmd List.mem_cons_self
    cases cmd with
    | call k a =>
      rcases hcmd with ⟨hk,ha⟩
      cases k with
      | zero =>
        exact ⟨hw',by simpa only [step,List.mem_cons,forall_eq_or_imp] using And.intro hz hv⟩
      | succ k =>
        have hh := he a ha
        cases h : expand a with
        | leaf b =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          exact ⟨hw',by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hh hv⟩
        | fork c x y =>
          simp only [h] at hh
          simp only [step,h,StateGood]
          refine ⟨?_,hv⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl|rfl|rfl|hd
          · exact ⟨by omega,hh.2.1⟩
          · exact ⟨by omega,hh.2.2⟩
          · exact hh.1
          · exact hw' d hd
    | join c =>
      cases v with
      | nil => exact ⟨by simp [step],hv⟩
      | cons y v =>
        cases v with
        | nil => exact ⟨by simp [step],hv⟩
        | cons x v =>
          simp only [step,StateGood]
          refine ⟨hw',?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl|hb
          · exact hc c hcmd x (hv x (by simp)) y (hv y (by simp))
          · exact hv b (by simp [hb])

lemma step_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) :
    (step zero expand combine s).1.length+(step zero expand combine s).2.length ≤ s.1.length+s.2.length+2 := by
  rcases s with ⟨w,v⟩
  cases w with
  | nil => simp [step]
  | cons cmd w =>
    cases cmd with
    | call k a =>
      cases k with
      | zero => simp [step]; omega
      | succ k => cases h : expand a <;> simp [step,h] <;> omega
    | join c => cases v with
      | nil => simp [step]
      | cons y v => cases v <;> simp [step]; omega

lemma iterate_length (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (s : State A B C) (j : ℕ) :
    ((step zero expand combine)^[j] s).1.length+((step zero expand combine)^[j] s).2.length ≤ s.1.length+s.2.length+2*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_length zero expand combine ((step zero expand combine)^[j] s)
    omega

lemma iterate_good (zero : B) (expand : A → Branch A B C) (combine : C → B → B → B)
    (K : ℕ) (PA : A → Prop) (PB : B → Prop) (PC : C → Prop)
    (hz : PB zero)
    (he : ∀ a,PA a → match expand a with | .leaf b => PB b | .fork c x y => PC c ∧ PA x ∧ PA y)
    (hc : ∀ c,PC c → ∀ x,PB x → ∀ y,PB y → PB (combine c x y))
    (s : State A B C) (hs : StateGood K PA PB PC s) (j : ℕ) :
    StateGood K PA PB PC ((step zero expand combine)^[j] s) := by
  induction j with
  | zero => exact hs
  | succ j ih => rw [Function.iterate_succ_apply']; exact step_good zero expand combine K PA PB PC hz he hc _ ih

lemma code_call {A C : Type} [Coding A] [Coding C] (k : ℕ) (a : A) :
    (encode (Command.call k a : Command A C)).length=8*k+4*(encode a).length+7 := by
  change (pairBits (pairBits (pairBits (encode k) (encode a)) []) []).length=_
  simp only [pairBits_length,List.length_nil,code_nat_length]
  omega
lemma code_join {A C : Type} [Coding A] [Coding C] (c : C) :
    (encode (Command.join c : Command A C)).length=2*(encode c).length+2 := by
  change (pairBits [] (pairBits (encode c) [])).length=_
  simp only [pairBits_length,List.length_nil]
  omega

lemma state_code_bound [Coding A] [Coding B] [Coding C] (s : State A B C) (M : ℕ)
    (hw : ∀ c∈s.1,(encode c).length≤M) (hv : ∀ b∈s.2,(encode b).length≤M) :
    (encode s).length≤2*(s.1.length+s.2.length)*(2*M+1)+1 := by
  have h₁ := list_code_bound s.1 M hw
  have h₂ := list_code_bound s.2 M hv
  rw [code_pair_length]
  nlinarith
end BinaryMatching.RecursiveEval
end

end OAI
