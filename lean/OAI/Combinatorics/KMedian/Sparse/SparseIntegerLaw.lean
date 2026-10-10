import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineElimination
import OAI.Combinatorics.KMedian.Compression.IntegerRationalCompression
import OAI.Combinatorics.KMedian.Geometry.TrimIntegerLaw

namespace OAI

namespace MetricKMedian
open Finset

structure SparseIntegerLaw (α : Type) where
  length : ℕ
  states : Vector α length
  law : IntegerLaw (Fin length)

namespace SparseIntegerLaw
variable {α : Type}

def moment (μ : SparseIntegerLaw α) (f : α → ℚ) : ℚ :=
  ∑ i : Fin μ.length, μ.law.rational.weight i*f μ.states[i.val]

def trim (μ : SparseIntegerLaw α) : SparseIntegerLaw α where
  length := μ.law.support.card
  states := Vector.ofFn (fun i => μ.states[(μ.law.support.orderEmbOfFin rfl i).val])
  law := μ.law.trim

theorem trim_moment (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.trim.moment f=μ.moment f := by
  unfold moment
  change (∑ i : Fin μ.law.support.card,
    μ.law.trim.rational.weight i * f ((Vector.ofFn (fun k =>
      μ.states[(μ.law.support.orderEmbOfFin rfl k).val]))[i.val])) = _
  simp only [Vector.getElem_ofFn]
  convert μ.law.trim_moment (fun i => f μ.states[i.val]) using 1

def compress {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ a j, |(v a j).num| ≤ (2:ℤ)^L)
    (hden : ∀ a j, ((v a j).den:ℤ) ≤ (2:ℤ)^L) : SparseIntegerLaw α :=
  let ν : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressRational (fun i => v μ.states[i.val]) L
      (fun i j => hnum _ j) (fun i j => hden _ j)⟩
  ν.trim

theorem compress_spec {d : ℕ} (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (L : ℕ) (hnum : ∀ a j, |(v a j).num| ≤ (2:ℤ)^L)
    (hden : ∀ a j, ((v a j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compress v L hnum hden
    ν.length ≤ d+1 ∧
      ν.law.denominator ≤ μ.law.denominator *
        (2:ℤ)^(((2*(d+1)*(d+1+L*(μ.length+1)))*(μ.length+1))*μ.length) ∧
      (∀ i : Fin ν.length, ∃ j : Fin μ.length, ν.states[i.val]=μ.states[j.val]) ∧
      ∀ j, ν.moment (fun a => v a j)=μ.moment (fun a => v a j) := by
  let ξ : SparseIntegerLaw α := ⟨μ.length,μ.states,
    μ.law.compressRational (fun i => v μ.states[i.val]) L
      (fun i j => hnum _ j) (fun i j => hden _ j)⟩
  have hh := μ.law.compressRational_spec (fun i => v μ.states[i.val]) L
    (fun i j => hnum _ j) (fun i j => hden _ j)
  refine ⟨hh.2.2.1,hh.1,?_,?_⟩
  · intro i
    refine ⟨ξ.law.support.orderEmbOfFin rfl i,?_⟩
    change (Vector.ofFn (fun k => μ.states[(ξ.law.support.orderEmbOfFin rfl k).val]))[i.val] = _
    simp only [Vector.getElem_ofFn]
    congr 2
  · intro j
    change ξ.trim.moment (fun a => v a j)=_
    rw [trim_moment]
    exact hh.2.2.2 j

end SparseIntegerLaw
end MetricKMedian

end OAI
