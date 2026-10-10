import Mathlib
import OAI.Combinatorics.KMedian.Geometry.BoundFreeCompression
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm

namespace OAI

section
section
namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

def prod (μ : IntegerLaw α) (ν : IntegerLaw β) : IntegerLaw (α × β) where
  denominator := μ.denominator*ν.denominator
  denominator_pos := mul_pos μ.denominator_pos ν.denominator_pos
  numerator := fun a => μ.numerator a.1*ν.numerator a.2
  numerator_nonneg a := mul_nonneg (μ.numerator_nonneg _) (ν.numerator_nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp only [← mul_sum,ν.total,← sum_mul,μ.total]

@[simp] theorem prod_weight (μ : IntegerLaw α) (ν : IntegerLaw β) (a : α) (b : β) :
    (μ.prod ν).rational.weight (a,b)=μ.rational.weight a*ν.rational.weight b := by
  simp only [prod,rational,Int.cast_mul]
  exact mul_div_mul_comm _ _ _ _

theorem prod_moment (μ : IntegerLaw α) (ν : IntegerLaw β) (f : α → β → ℚ) :
    (∑ ab, (μ.prod ν).rational.weight ab*f ab.1 ab.2)=
      ∑ a, μ.rational.weight a*(∑ b, ν.rational.weight b*f a b) := by
  rw [Fintype.sum_prod_type]
  simp only [prod_weight,mul_sum,mul_assoc]

end MetricKMedian.IntegerLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

def prod (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β) (f : α → β → γ) : SparseIntegerLaw γ where
  length := μ.length*ν.length
  states := Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val])
  law := (μ.law.prod ν.law).reindex (finProdFinEquiv (m := μ.length) (n := ν.length))

theorem prod_moment (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → ℚ) :
    (μ.prod ν f).moment v=μ.moment (fun a => ν.moment (fun b => v (f a b))) := by
  have h := (μ.law.prod ν.law).reindex_moment (finProdFinEquiv (m := μ.length) (n := ν.length))
    (fun a => v (f μ.states[a.1.val] ν.states[a.2.val]))
  have h' := μ.law.prod_moment ν.law (fun a b => v (f μ.states[a.val] ν.states[b.val]))
  unfold moment prod
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1

theorem prod_property (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (P : γ → Prop)
    (hP : ∀ a : Fin μ.length, ∀ b : Fin ν.length, P (f μ.states[a.val] ν.states[b.val])) :
    ∀ a : Fin (μ.prod ν f).length, P (μ.prod ν f).states[a.val] := by
  intro a
  change P ((Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val]))[a.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

def prodCompress {d : ℕ} (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → Fin d → ℚ) : SparseIntegerLaw γ :=
  (μ.prod ν f).compressAuto v

theorem prodCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (v : γ → Fin d → ℚ) :
    let ρ := μ.prodCompress ν f v
    ρ.length ≤ d+1 ∧
    (∀ a : Fin ρ.length, ∃ b : Fin μ.length, ∃ c : Fin ν.length,
      ρ.states[a.val]=f μ.states[b.val] ν.states[c.val]) ∧
    ∀ j, ρ.moment (fun t => v t j)=μ.moment (fun a => ν.moment (fun b => v (f a b) j)) := by
  have h := (μ.prod ν f).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (prod_moment μ ν f _)⟩
  intro a
  obtain ⟨b,hb⟩ := h.2.1 a
  refine ⟨((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).1,((finProdFinEquiv (m := μ.length) (n := ν.length)).symm b).2,?_⟩
  exact hb.trans (by
    simp only [prod,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
