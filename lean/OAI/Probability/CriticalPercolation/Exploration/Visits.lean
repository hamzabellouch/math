import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Node

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteEntropy

variable {E : Type*}

def visits (t : QueryTree E) (n : t.Node) (ω : E → Bool) : Bool :=
  (t.response n (t.run ω)).isSome

lemma response_run (t : QueryTree E) (n : t.Node) (ω : E → Bool) :
    t.response n (t.run ω) = if t.visits n ω then some (ω (t.bit n)) else none := by
  induction t with
  | stop => exact PEmpty.elim n
  | ask e l r hl hr =>
    rcases n with n | n
    · cases he : ω e <;> simp [run, response, visits, bit, he]
    · rcases n with n | n
      · cases he : ω e
        · have ih := hl n
          simp only [run, he, Bool.false_eq_true, ↓reduceIte, visits, response, bit] at ih ⊢
          convert ih using 1
          split_ifs <;> simp_all
        · simp [run, visits, response, he]
      · cases he : ω e
        · simp [run, visits, response, he]
        · have ih := hr n
          simp only [run, he, ↓reduceIte, visits, response, bit] at ih ⊢
          convert ih using 1
          split_ifs <;> simp_all

lemma bit_not_mem [DecidableEq E] (t : QueryTree E) (used : Finset E)
    (hv : t.Valid used) (n : t.Node) : t.bit n ∉ used := by
  induction t generalizing used with
  | stop => exact PEmpty.elim n
  | ask e l r hl hr =>
    rcases n with n | n
    · exact hv.1
    · rcases n with n | n
      · exact fun hm => hl _ hv.2.1 n (Finset.mem_insert_of_mem hm)
      · exact fun hm => hr _ hv.2.2 n (Finset.mem_insert_of_mem hm)

lemma nodeMass_push [Fintype E] (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.nodeMass (pushMass t.run P) n = ∑ ω, if t.visits n ω then P ω else 0 := by
  have h := sum_pushMass_mul t.run P (fun x => if (t.response n x).isSome then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  unfold nodeMass visits
  convert h using 1

lemma nodeTrueMass_push [Fintype E] (t : QueryTree E) (P : (E → Bool) → ℝ) (n : t.Node) :
    t.nodeTrueMass (pushMass t.run P) n =
      ∑ ω, if t.visits n ω ∧ ω (t.bit n) = true then P ω else 0 := by
  have h := sum_pushMass_mul t.run P (fun x => if t.response n x = some true then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [nodeTrueMass, h]
  apply Finset.sum_congr rfl
  intro ω _
  rw [response_run]
  split_ifs <;> simp_all

lemma quadratic_charge_eq_sum (p : ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge (fun r => (r-p)^2) P =
      ∑ n, (t.nodeTrueMass P n - p*t.nodeMass P n)^2 / t.nodeMass P n := by
  rw [charge_eq_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hz : t.nodeMass P n = 0
  · simp [hz]
  · field_simp

end CriticalPercolation.QueryTree

namespace CriticalPercolation
universe u v w

inductive MarkedTree (E : Type u) (A : Type v) : Type (max u v) where
  | stop : MarkedTree E A
  | ask (e : E) (tag : A) (left right : MarkedTree E A) : MarkedTree E A

namespace MarkedTree
variable {E : Type u} {A : Type v} {B : Type w}

def bare : MarkedTree E A → QueryTree E
  | .stop => .stop
  | .ask e _ l r => .ask e l.bare r.bare

def nodeLabel : (t : MarkedTree E A) → t.bare.Node → A
  | .stop, n => PEmpty.elim n
  | .ask _ a _ _, .inl _ => a
  | .ask _ _ l _, .inr (.inl n) => l.nodeLabel n
  | .ask _ _ _ r, .inr (.inr n) => r.nodeLabel n

def trace : MarkedTree E A → (E → Bool) → List (E × A)
  | .stop, _ => []
  | .ask e a l r, ω => (e,a) :: if ω e then r.trace ω else l.trace ω

def map (f : A → B) : MarkedTree E A → MarkedTree E B
  | .stop => .stop
  | .ask e a l r => .ask e (f a) (l.map f) (r.map f)

lemma trace_map (f : A → B) (t : MarkedTree E A) (ω : E → Bool) :
    (t.map f).trace ω = (t.trace ω).map (fun x => (x.1, f x.2)) := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [map, trace, h, hl, hr]

lemma trace_bits (t : MarkedTree E A) (ω : E → Bool) :
    (t.trace ω).map Prod.fst = t.bare.reads ω := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [trace, bare, QueryTree.reads, h, hl, hr]

def append : MarkedTree E A → MarkedTree E A → MarkedTree E A
  | .stop, s => s
  | .ask e a l r, s => .ask e a (l.append s) (r.append s)

lemma trace_append (t s : MarkedTree E A) (ω : E → Bool) :
    (t.append s).trace ω = t.trace ω ++ s.trace ω := by
  induction t with
  | stop => rfl
  | ask e a l r hl hr => cases h : ω e <;> simp [append, trace, h, hl, hr]

def sequence : List (MarkedTree E A) → MarkedTree E A
  | [] => .stop
  | t :: ts => t.append (sequence ts)

lemma trace_sequence (ts : List (MarkedTree E A)) (ω : E → Bool) :
    (sequence ts).trace ω = (ts.map (fun t => t.trace ω)).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [sequence, trace_append, ih]

variable [DecidableEq E]

abbrev Cache (E : Type u) := E → Option Bool

def Compatible (σ : Cache E) (ω : E → Bool) : Prop :=
  ∀ e b, σ e = some b → ω e = b

lemma compatible_update (σ : Cache E) (ω : E → Bool) (hσ : Compatible σ ω) (e : E) :
    Compatible (Function.update σ e (some (ω e))) ω := by
  intro f b hb
  by_cases h : f = e
  · subst f
    simpa using hb
  · exact hσ f b (by simpa [Function.update, h] using hb)

def cached : MarkedTree E A → Cache E → MarkedTree E A
  | .stop, _ => .stop
  | .ask e a l r, σ =>
    match σ e with
    | some false => l.cached σ
    | some true => r.cached σ
    | none => .ask e a
        (l.cached (Function.update σ e (some false)))
        (r.cached (Function.update σ e (some true)))

def fresh (ω : E → Bool) : Cache E → List (E × A) → List (E × A)
  | _, [] => []
  | σ, x :: xs =>
    let rest := fresh ω (Function.update σ x.1 (some (ω x.1))) xs
    if (σ x.1).isNone then x :: rest else rest

lemma update_compatible_value (σ : Cache E) (e : E) (b : Bool) (h : σ e = some b) :
    Function.update σ e (some b) = σ := by
  ext f
  by_cases hf : f = e
  · subst f; simp [h]
  · simp [Function.update, hf]

lemma trace_cached (t : MarkedTree E A) (σ : Cache E) (ω : E → Bool)
    (hσ : Compatible σ ω) :
    (t.cached σ).trace ω = fresh ω σ (t.trace ω) := by
  induction t generalizing σ with
  | stop => rfl
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      cases he : ω e
      · simpa [cached, hs, trace, he, fresh] using hl
          (Function.update σ e (some false)) (by simpa [he] using compatible_update σ ω hσ e)
      · simpa [cached, hs, trace, he, fresh] using hr
          (Function.update σ e (some true)) (by simpa [he] using compatible_update σ ω hσ e)
    | some b =>
      have he := hσ e b hs
      have hu := update_compatible_value σ e b hs
      cases b
      · simpa [cached, hs, trace, he, fresh, hu] using hl σ hσ
      · simpa [cached, hs, trace, he, fresh, hu] using hr σ hσ

variable [Fintype E]

noncomputable def domain (σ : Cache E) : Finset E :=
  Finset.univ.filter (fun e => (σ e).isSome)

omit [DecidableEq E] in
lemma mem_domain (σ : Cache E) (e : E) : e ∈ domain σ ↔ (σ e).isSome := by
  simp [domain]

lemma domain_update (σ : Cache E) (e : E) (b : Bool) :
    domain (Function.update σ e (some b)) = insert e (domain σ) := by
  ext f
  by_cases hf : f = e
  · subst f; simp [mem_domain]
  · simp [mem_domain, Function.update, hf]

lemma cached_valid (t : MarkedTree E A) (σ : Cache E) :
    (t.cached σ).bare.Valid (domain σ) := by
  induction t generalizing σ with
  | stop => trivial
  | ask e a l r hl hr =>
    cases hs : σ e with
    | none =>
      simp only [cached, hs, bare, QueryTree.Valid]
      refine ⟨?_, ?_, ?_⟩
      · simp [mem_domain, hs]
      · simpa only [domain_update σ e false] using hl (Function.update σ e (some false))
      · simpa only [domain_update σ e true] using hr (Function.update σ e (some true))
    | some b =>
      cases b
      · simpa only [cached, hs] using hl σ
      · simpa only [cached, hs] using hr σ

lemma cached_empty_valid (t : MarkedTree E A) :
    (t.cached (fun _ => none)).bare.Valid ∅ := by
  simpa [domain] using cached_valid t (fun _ => none)

end MarkedTree
end CriticalPercolation

end
end

end OAI
