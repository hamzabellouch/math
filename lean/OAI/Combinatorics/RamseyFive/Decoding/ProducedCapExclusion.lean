import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.PublicCapLaw
import OAI.Combinatorics.RamseyFive.Entropy.FreshProcess

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma eventMass_map_filter (p : Law α) (f : α→β) (P : β→Prop) :
    eventMass (map p f) (Finset.univ.filter P)=
    eventMass p (Finset.univ.filter fun a=>P (f a)) := by
  simpa only [eventMass,Finset.sum_filter,mul_ite,mul_one,mul_zero] using
    sum_map p f (fun b=>if P b then (1:ℝ) else 0)
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

def Excludes (a : A) : Option (Finset A)→Prop
  | none => False
  | some Y => a∉Y

lemma publicCapLaw_exclusion (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) (a : A) (ha : a∈U) :
    eventMass (publicCapLaw R S U C W hW n q M) (Finset.univ.filter (Excludes a))=
    freshRejection (fun b a=>R a b) q W hW n (uniformCutoff q C W n)
      (validationRows R S U C n q M) a := by
  unfold publicCapLaw freshRejection
  rw [eventMass_map_filter]
  apply congrArg (eventMass _)
  apply Finset.ext
  intro row
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,Finset.mem_image]
  cases row with
  | none => simp only [Option.map_none,Excludes,Option.some_ne_none,and_false,exists_false]
  | some row =>
    simp only [Option.map_some,Excludes,Finset.mem_filter,cap,ha,true_and,not_lt,
      Option.some.injEq,exists_eq_right,Finset.mem_univ,true_and]
    change hits (neighbors R a) row ≥ (n:ℝ)/(5*q) ↔ _
    rw [show (n:ℝ)/(5*q)=(1/(5*q))*n by ring]
    rfl

theorem publicCapLaw_domination (R : A→B→Prop) (S U : Finset A)
    (C X W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (hCX : C⊆X) (n : ℕ) (hn : 0<n)
    (q c M : ℝ) (hq : 0<q) (hc : 0<c) (hsize : c*X.card≤C.card)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) (a : A) (ha : a∈U) :
    eventMass (publicCapLaw R S U C W hW n q M) (Finset.univ.filter (Excludes a))≤
      (50*q/(9*c))*(((X.filter (R a)).card:ℝ)/X.card) := by
  rw [publicCapLaw_exclusion R S U C W hW n q M a ha]
  have h := fresh_test_domination C X W (Finset.univ.filter (R a)) hC hW hCW hCX
    q c hq hc hsize n (uniformCutoff q C W n) hn (uniformCutoff_pos q hq C W hC hW n)
    (validationRows R S U C n q M) (fun row hr=>(Finset.mem_filter.mp hr).2.1) hE
  have he : (Finset.univ.filter (R a))∩X=X.filter (R a) := by ext b;simp [and_comm]
  simpa only [freshRejection,he] using h

end SharpRamseyFive.ReverseCap

end OAI
