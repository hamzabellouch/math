import Mathlib
import OAI.Combinatorics.UniformKServer.StarAllocator
import OAI.Combinatorics.UniformKServer.TreeRankData

namespace OAI

                                    
section

/-! Top-down propagation on the fixed finite tree, with literal causal star
outputs. Repeated and empty leaf counts are not excluded. -/
noncomputable section
namespace UniformKServer.TreeAllocator
open Finset TreeRounding TreeRankData
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

def amount (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) : ℝ :=
  if hv : v=0 then k else
    StarAllocator.output (star d (S.parent v)) hk t ω (amount d hk t ω (S.parent v)) ⟨v,hv,rfl⟩
termination_by v.val
decreasing_by exact S.earlier v hv

theorem root (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : amount d hk t ω 0=k := by
  rw [amount,dite_eq_left rfl]

theorem child (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) (i : Children S v) :
    amount d hk t ω i.val=StarAllocator.output (star d v) hk t ω (amount d hk t ω v) i := by
  rcases i with ⟨u,hu,hp⟩
  subst v
  rw [amount,dite_eq_right hu]

theorem lower_le (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    lower d v t ω ≤ amount d hk t ω v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v
      rw [root]
      exact lower_bound d hk 0 t ω
    · let i : Children S (S.parent v) := ⟨v,hv,rfl⟩
      have hp := (parent_le_lower d hk (S.parent v) t ω).trans
        (ih (S.parent v) (S.earlier v hv))
      have h := (StarAllocator.feasible (star d (S.parent v)) hk t ω hp).1 i
      rw [child_lower] at h
      rw [←child d hk t ω (S.parent v) i] at h
      exact h

theorem parent_le (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    StarLower.parentLower (star d v) t ω ≤ amount d hk t ω v :=
  (parent_le_lower d hk v t ω).trans (lower_le d hk t ω v)

theorem nonneg (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    0 ≤ amount d hk t ω v := (lower_nonneg d hk v t ω).trans (lower_le d hk t ω v)

theorem budget (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (v : Vertex n) :
    (∑ i : Children S v, amount d hk t ω i.val) ≤ amount d hk t ω v := by
  simp only [child]
  exact (StarAllocator.feasible (star d v) hk t ω (parent_le d hk t ω v)).2.2

def allocation (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : Allocation S k where
  amount := amount d hk t ω
  nonneg := nonneg d hk t ω
  park_nonneg := fun v => sub_nonneg.mpr (budget d hk t ω v)
  root := root d hk t ω

theorem measurable (d : Data Ω S k) (hk : 1 ≤ k) (t : ℕ) {ω x : Ω}
    (hx : (d.filtration t).r ω x) (v : Vertex n) : amount d hk t ω v=amount d hk t x v := by
  induction v using WellFounded.induction (measure Fin.val).wf with
  | h v ih =>
    by_cases hv : v=0
    · subst v; rw [root,root]
    · conv_lhs => rw [amount]
      conv_rhs => rw [amount]
      rw [dite_eq_right hv,dite_eq_right hv,ih (S.parent v) (S.earlier v hv),
        StarAllocator.measurable (star d (S.parent v)) hk t hx]

end UniformKServer.TreeAllocator

end


end

end OAI
