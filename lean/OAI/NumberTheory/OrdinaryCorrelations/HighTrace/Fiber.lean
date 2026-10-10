import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SizedSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.TypeFibers
open Finset Classical
variable {P T : Type*} [Fintype P] [Fintype T]

def fiber (f : P → Option T) (t : T) : Finset P := univ.filter (fun p => f p = some t)

def multiplicity (f : P → Option T) (t : T) : ℕ := (fiber f t).card

def unordered (f : P → Option T) : FactorialAssignments.Unordered (P := P) (multiplicity f) :=
  fun t => ⟨fiber f t,rfl⟩

omit [Fintype T] in
lemma mem_fiber (f : P → Option T) (p : P) (t : T) : p ∈ fiber f t ↔ f p = some t := by
  simp [fiber]

omit [Fintype T] in
lemma fibers_disjoint (f : P → Option T) {s t : T} (hst : s ≠ t) :
    Disjoint (fiber f s) (fiber f t) := by
  apply disjoint_left.mpr
  intro p hs ht
  exact hst (Option.some.inj ((mem_fiber f p s).mp hs |>.symm.trans ((mem_fiber f p t).mp ht)))

def factor (f : P → Option T) (W : T → P → ℝ) (p : P) : ℝ :=
  match f p with | none => 1 | some t => W t p

lemma fiber_product (f : P → Option T) (W : T → P → ℝ) :
    (∏ t : T, ∏ p ∈ fiber f t, W t p) = ∏ p : P, factor f W p := by
  simp only [fiber,prod_filter]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro p hp
  rcases he : f p with _ | t
  · simp [he,factor]
  · rw [factor,he]
    rw [prod_eq_single t]
    · simp
    · intro u hu hut
      exact ite_eq_right (fun hyp => hut (Option.some.inj hyp).symm)
    · simp

theorem unorderedWeight_eq (f : P → Option T) (W : T → P → ℝ) :
    FactorialAssignments.unorderedWeight (multiplicity f) W (unordered f) =
      ∏ p, factor f W p := fiber_product f W

end OrdinaryCorrelations.TypeFibers

end

end OAI
