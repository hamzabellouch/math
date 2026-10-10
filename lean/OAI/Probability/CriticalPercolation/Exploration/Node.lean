import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.BitWeight

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
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (e : E) (b : Bool) :
    0 < bitWeight p e b := by
  cases b <;> simp [bitWeight, hp.1, hp.2]

theorem transcript_divergence_le {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (hv : t.Valid ∅) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) :
    divergence (pushMass t.run P) (t.reference p) ≤ divergence P (density (bitWeight p)) := by
  rw [← reference_eq_product_push p t ∅ hv]
  exact divergence_pushMass_le t.run P _ hP
    (density_nonneg (bitWeight_nonneg ⟨hp.1.le, hp.2.le⟩))
    (fun ω _ => Finset.prod_pos fun e _ => bitWeight_pos hp e (ω e))

theorem quadratic_bias_budget {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (hv : t.Valid ∅) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1) :
    2*t.charge (fun r => (r-p)^2) (pushMass t.run P) ≤
      divergence P (density (bitWeight p)) := by
  exact (divergence_reference_bounds hp t _ (pushMass_nonneg t.run P hP)
    (by rw [pushMass_sum, hMass])).1.trans (transcript_divergence_le hp t hv P hP)

theorem transcript_divergence_upper {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : QueryTree E) (P : (E → Bool) → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1) :
    divergence (pushMass t.run P) (t.reference p) ≤
      (p*(1-p))⁻¹*t.charge (fun r => (r-p)^2) (pushMass t.run P) := by
  exact (divergence_reference_bounds hp t _ (pushMass_nonneg t.run P hP)
    (by rw [pushMass_sum, hMass])).2

end CriticalPercolation.QueryTree

namespace CriticalPercolation.QueryTree
variable {E : Type*}

@[reducible] def Node : QueryTree E → Type
  | .stop => PEmpty
  | .ask _ l r => PUnit ⊕ (l.Node ⊕ r.Node)

instance nodeFintype : (t : QueryTree E) → Fintype t.Node
  | .stop => inferInstanceAs (Fintype PEmpty)
  | .ask _ l r => @instFintypeSum _ _ (inferInstanceAs (Fintype PUnit))
      (@instFintypeSum _ _ l.nodeFintype r.nodeFintype)

def bit : (t : QueryTree E) → t.Node → E
  | .stop, n => PEmpty.elim n
  | .ask e _ _, .inl _ => e
  | .ask _ l _, .inr (.inl n) => l.bit n
  | .ask _ _ r, .inr (.inr n) => r.bit n

def response : (t : QueryTree E) → t.Node → t.Leaf → Option Bool
  | .stop, n, _ => PEmpty.elim n
  | .ask _ _ _, .inl _, .inl _ => some false
  | .ask _ _ _, .inl _, .inr _ => some true
  | .ask _ l _, .inr (.inl n), .inl x => l.response n x
  | .ask _ _ _, .inr (.inl _), .inr _ => none
  | .ask _ _ _, .inr (.inr _), .inl _ => none
  | .ask _ _ r, .inr (.inr n), .inr x => r.response n x

noncomputable def nodeMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if (t.response n x).isSome then P x else 0

noncomputable def nodeTrueMass (t : QueryTree E) (P : t.Leaf → ℝ) (n : t.Node) : ℝ :=
  ∑ x, if t.response n x = some true then P x else 0

lemma nodeMass_root (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (z : PUnit) :
    (ask e l r).nodeMass P (.inl z) =
      (∑ x, P (.inl x)) + ∑ x, P (.inr x) := by
  simp [nodeMass, response, Fintype.sum_sum_type]

lemma nodeTrueMass_root (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (z : PUnit) :
    (ask e l r).nodeTrueMass P (.inl z) = ∑ x, P (.inr x) := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]

lemma nodeMass_left (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : l.Node) :
    (ask e l r).nodeMass P (.inr (.inl n)) = l.nodeMass (fun x => P (.inl x)) n := by
  simp [nodeMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeTrueMass_left (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : l.Node) :
    (ask e l r).nodeTrueMass P (.inr (.inl n)) = l.nodeTrueMass (fun x => P (.inl x)) n := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeMass_right (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : r.Node) :
    (ask e l r).nodeMass P (.inr (.inr n)) = r.nodeMass (fun x => P (.inr x)) n := by
  simp [nodeMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma nodeTrueMass_right (e : E) (l r : QueryTree E) (P : (ask e l r).Leaf → ℝ) (n : r.Node) :
    (ask e l r).nodeTrueMass P (.inr (.inr n)) = r.nodeTrueMass (fun x => P (.inr x)) n := by
  simp [nodeTrueMass, response, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

lemma charge_eq_sum (F : ℝ → ℝ) (t : QueryTree E) (P : t.Leaf → ℝ) :
    t.charge F P = ∑ n, t.nodeMass P n * F (t.nodeTrueMass P n / t.nodeMass P n) := by
  induction t with
  | stop => simp [charge, Node]
  | ask e l r hl hr =>
    change _ = ∑ n : PUnit ⊕ (l.Node ⊕ r.Node), _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, nodeMass_root, nodeTrueMass_root,
      nodeMass_left, nodeTrueMass_left, nodeMass_right, nodeTrueMass_right]
    rw [← hl, ← hr]
    simp only [charge]
    ring

end CriticalPercolation.QueryTree

end
end

end OAI
