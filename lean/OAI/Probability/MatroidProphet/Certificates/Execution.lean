import OAI.Probability.MatroidProphet.Certificates.Budget

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

def QueryProgram.run (cert : Finset α → Prop) [DecidablePred cert]
    (S : Finset α) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => if e ∈ S then yes.run cert S (insert e I) else no.run cert S I
  | .finish rest, I => (if cert I then 1 else 0) + rest.run cert S ∅

lemma QueryProgram.run_congr (cert : Finset α → Prop) [DecidablePred cert]
    (prog : QueryProgram α) (V I S S' : Finset α) (fresh : prog.Fresh V)
    (agree : ∀ e ∈ V, (e ∈ S ↔ e ∈ S')) :
    prog.run cert S I = prog.run cert S' I := by
  induction prog generalizing V I with
  | stop => rfl
  | finish rest ih =>
    simp only [run]
    rw [ih V ∅ fresh agree]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have ha := agree e he
    have har : ∀ x ∈ V.erase e, (x ∈ S ↔ x ∈ S') :=
      fun x hx => agree x (mem_of_mem_erase hx)
    by_cases h : e ∈ S
    · simp only [run, ite_eq_left h, ite_eq_left (ha.mp h)]
      exact ihy (V.erase e) (insert e I) hy har
    · have h' : e ∉ S' := fun hx => h (ha.mpr hx)
      simp only [run, ite_eq_right h, ite_eq_right h']
      exact ihn (V.erase e) I hn har

lemma QueryProgram.expected_eq_product (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    bitsExpectation q V (fun S => prog.run cert S I) = prog.expected cert q I := by
  induction prog generalizing V I with
  | stop => simp only [run, expected, bitsExpectation_const]
  | finish rest ih =>
    simp only [run, expected, bitsExpectation_add, bitsExpectation_const]
    rw [ih V ∅ fresh]
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hsplit := bitsExpectation_insert q (V.erase e) e (notMem_erase e V)
      (fun S => (QueryProgram.query e no yes).run cert S I)
    rw [insert_erase he] at hsplit
    have hno : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert S I) =
        bitsExpectation q (V.erase e) (fun S => no.run cert S I) := by
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun hx => (notMem_erase e V) (hS hx)
      simp only [run, ite_eq_right heS]
    have hyes : bitsExpectation q (V.erase e)
        (fun S => (QueryProgram.query e no yes).run cert (insert e S) I) =
        bitsExpectation q (V.erase e) (fun S => yes.run cert S (insert e I)) := by
      apply bitsExpectation_congr
      intro S hS
      simp only [run, mem_insert_self, ite_true]
      apply yes.run_congr cert (V.erase e) (insert e I) (insert e S) S hy
      intro x hx
      have hxe : x ≠ e := (mem_erase.1 hx).1
      simp only [mem_insert, hxe, false_or]
    rw [hsplit, hno, hyes, ihn (V.erase e) I hn, ihy (V.erase e) (insert e I) hy]
    rfl

theorem disjoint_query_certificates_product [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    bitsExpectation q univ (fun S => prog.run cert S ∅) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := by
  rw [prog.expected_eq_product cert q univ ∅ fresh]
  exact disjoint_query_certificates cert hcert q hq0 hq1 hδ prog fresh

end MatroidProphet

end OAI
