import Mathlib
import OAI.Combinatorics.KMedian.Geometry.BoundFreeCompression
import OAI.Combinatorics.KMedian.Sparse.SparseIntegerLaw
import OAI.Combinatorics.KMedian.Geometry.IntegerBranching

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

def branch (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) : SparseIntegerLaw α where
  length := μ.length*2
  states := Vector.ofFn (fun i => next
    μ.states[(finProdFinEquiv.symm i).1.val] (finProdFinEquiv.symm i).2)
  law := (IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])).reindex finProdFinEquiv

theorem branch_moment (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) (f : α → ℚ) :
    (μ.branch p hp next).moment f=
      μ.moment (fun a => p a*f (next a 0)+(1-p a)*f (next a 1)) := by
  let ρ := IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])
  have h := ρ.reindex_moment finProdFinEquiv
    (fun a => f (next μ.states[a.1.val] a.2))
  have h' := IntegerBranching.branch_moment μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val]) (fun i b => f (next μ.states[i.val] b))
  unfold moment branch
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1

def compressAuto {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ) :
    SparseIntegerLaw α :=
  let ν : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressAuto (fun i => v μ.states[i.val])⟩
  ν.trim

theorem compressAuto_correct {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.length ≤ d+1 ∧
      (∀ i : Fin ν.length, ∃ j : Fin μ.length, ν.states[i.val]=μ.states[j.val]) ∧
      ∀ j, ν.moment (fun a => v a j)=μ.moment (fun a => v a j) := by
  let ξ : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressAuto (fun i => v μ.states[i.val])⟩
  have hh := μ.law.compressAuto_correct (fun i => v μ.states[i.val])
  refine ⟨hh.2.1,?_,?_⟩
  · intro i
    refine ⟨ξ.law.support.orderEmbOfFin rfl i,?_⟩
    change (Vector.ofFn (fun k => μ.states[(ξ.law.support.orderEmbOfFin rfl k).val]))[i.val] = _
    simp only [Vector.getElem_ofFn]
    congr 2
  · intro j
    change ξ.trim.moment (fun a => v a j)=_
    rw [trim_moment]
    exact hh.2.2 j

theorem compressAuto_denominator {d : ℕ} (μ : SparseIntegerLaw α)
    (v : α → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i : Fin μ.length, ∀ j, |(v μ.states[i.val] j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i : Fin μ.length, ∀ j, ((v μ.states[i.val] j).den:ℤ) ≤ (2:ℤ)^L) :
    (μ.compressAuto v).law.denominator ≤ μ.law.denominator *
      (2:ℤ)^(((2*(d+1)*(d+1+L*(μ.length+1)))*(μ.length+1))*μ.length) :=
  (μ.law.compressAuto_spec (fun i => v μ.states[i.val]) L hnum hden).1

def step {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) :
    SparseIntegerLaw α := (μ.branch p hp next).compressAuto v

theorem step_moment {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (j : Fin d) :
    (step v μ p hp next).moment (fun a => v a j)=
      μ.moment (fun a => p a*v (next a 0) j+(1-p a)*v (next a 1) j) :=
  ((μ.branch p hp next).compressAuto_correct v).2.2 j |>.trans
    (μ.branch_moment p hp next _)

theorem step_property {d : ℕ} (v : α → Fin d → ℚ) (μ : SparseIntegerLaw α)
    (p : α → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α)
    (P : α → Prop) (hP : ∀ i : Fin μ.length, ∀ b, P (next μ.states[i.val] b)) :
    ∀ i : Fin (step v μ p hp next).length, P (step v μ p hp next).states[i.val] := by
  intro i
  obtain ⟨j,hj⟩ := ((μ.branch p hp next).compressAuto_correct v).2.1 i
  change P ((μ.branch p hp next).compressAuto v).states[i.val]
  rw [hj]
  change P ((Vector.ofFn (fun k => next
    μ.states[(finProdFinEquiv.symm k).1.val] (finProdFinEquiv.symm k).2))[j.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw

end OAI
