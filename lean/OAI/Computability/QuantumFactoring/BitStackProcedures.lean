import Mathlib
import OAI.Computability.QuantumFactoring.BitStackPrograms

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

lemma Runs.length_le {p : Program K} {s t : Store K} {c : ℕ} (h : Runs p s t c) (k : K) :
    (t k).length ≤ (s k).length+c := by
  induction h with
  | skip s => omega
  | push s a b =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self,List.length_cons]; omega
    · simp only [Function.update_of_ne hk]; omega
  | seq hp hq ip iq => omega
  | cases_nil hs hr ih => omega
  | @cases_false a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | @cases_true a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | loop_nil hs => omega
  | @loop_false a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega
  | @loop_true a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega

/-- A completely explicit finite-state Boolean-stack subroutine, with the
same clean input/output convention as the frozen TM2 uniformity target. -/
structure Procedure {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  K : Type
  finiteK : Fintype K
  decideK : DecidableEq K
  input : K
  output : K
  program : Program K
  bound : Polynomial ℕ
  runs : ∀ a, ∃ c, c ≤ bound.eval (ea a).length ∧
    @Runs K decideK program (@singletonStore K decideK input (ea a)) (@singletonStore K decideK output (eb (f a))) c

attribute [instance] Procedure.finiteK Procedure.decideK
namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma output_length_le (p : Procedure ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length+p.bound.eval (ea a).length := by
  obtain ⟨c,hc,hr⟩ := p.runs a
  have h := hr.length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases he : p.output=p.input
  · simp only [he,Function.update_self] at h; omega
  · simp only [Function.update_of_ne he,List.length_nil,Nat.zero_add] at h; omega

noncomputable def toTM2 (p : Procedure ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := machine p.input p.output p.program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.bound+1
  outputsFun a := by
    classical
    let c := Classical.choose (p.runs a)
    have hc := (Classical.choose_spec (p.runs a)).1
    have hr := (Classical.choose_spec (p.runs a)).2
    have h := machine_outputs p.input p.output p.program (ea a) (eb (f a)) c hr
    have ht : Turing.TM2OutputsInTime (machine p.input p.output p.program)
        (ea a) (some (eb (f a))) (p.bound.eval (ea a).length+1) :=
      ⟨h.1, h.2.trans (Nat.add_le_add_right hc 1)⟩
    convert ht using 1
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

lemma toTM2_finite (p : Procedure ea eb f) : ∀ k, Finite (p.toTM2.tm.Γ k) :=
  machine_alphabets_finite _ _ _
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
