import OAI.Probability.MatroidProphet.Main
import Mathlib.Combinatorics.Matroid.Map

namespace OAI

namespace MatroidProphet.Relabeling

open Finset

/-- The offline benchmark on an arbitrary finite label type. -/
noncomputable def finiteOptimum {α : Type*} [Fintype α]
    (M : Matroid α) (w : α → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset α => if M.Indep (I : Set α) then ∑ e ∈ I, w e else 0)

/-- Reindex all weights, retaining every label including loops and zero weights. -/
def encodeWeights {α β : Type*} (e : α ≃ β) (w : α → ℝ) : β → ℝ :=
  fun b => w (e.symm b)

/-- Every sample and online coordinate, indexed by original label and copy. -/
def labeledPairedCoordinates {α Ω : Type*} (S V : Ω → α → ℝ)
    (i : α × Bool) : Ω → ℝ :=
  if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1

/-- An arrival order on `α` lists every label exactly once. -/
abbrev LabeledOrder (α : Type*) (n : ℕ) := Fin n ≃ α

/-- The available prefix, with arbitrary original labels. -/
abbrev LabeledHistory (α : Type*) {n : ℕ} (k : Fin n) :=
  Fin (k.val + 1) → α × ℝ

/-- Reindex the labels of an observed history without changing any observed value. -/
def encodeHistory {α : Type*} {n : ℕ} (e : α ≃ Fin n) (k : Fin n)
    (h : LabeledHistory α k) : History n k :=
  fun j => (e (h j).1, (h j).2)

/-- The history supplied by a genuine arrival stream on the original labels. -/
def labeledHistory {α : Type*} {n : ℕ} (w : α → ℝ)
    (π : LabeledOrder α n) (k : Fin n) : LabeledHistory α k :=
  fun j => let a := π (prefixIndex k j); (a, w a)

/-- The transported decision uses only the seed, original samples, and history. -/
def transportedDecision {α : Type*} {n bits : ℕ} (e : α ≃ Fin n)
    (A : OnlineRule n bits) (k : Fin n) (r : Seed bits)
    (s : α → ℝ) (h : LabeledHistory α k) : Bool :=
  A.decide k r (encodeWeights e s) (encodeHistory e k h)

/-- Irrevocable accepted labels in the original labeled stream. -/
noncomputable def transportedAcceptedThrough {α : Type*} [Fintype α]
    {n bits : ℕ} (e : α ≃ Fin n) (A : OnlineRule n bits)
    (r : Seed bits) (s v : α → ℝ) (π : LabeledOrder α n) (t : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter fun a => (π.symm a).val < t ∧
    transportedDecision e A (π.symm a) r s (labeledHistory v π (π.symm a)) = true

/-- Real reward, with no rounding or loss in the relabeling. -/
noncomputable def transportedReward {α : Type*} [Fintype α]
    {n bits : ℕ} (e : α ≃ Fin n) (A : OnlineRule n bits)
    (r : Seed bits) (s v : α → ℝ) (π : LabeledOrder α n) : ℝ :=
  ∑ a ∈ transportedAcceptedThrough e A r s v π n, v a

end MatroidProphet.Relabeling

end OAI
