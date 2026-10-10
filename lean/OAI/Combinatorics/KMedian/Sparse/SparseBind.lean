import Mathlib
import OAI.Combinatorics.KMedian.Compression.RationalIntegerLaw
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {α : Type} {β : α → Type} [Fintype α] [∀ a, Fintype (β a)]

def sigma (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) : RationalLaw (Sigma β) where
  weight z := μ.weight z.1*(κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg _) ((κ _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← mul_sum]
    calc
      _ = ∑ a, μ.weight a := sum_congr rfl (fun a _ => by rw [(κ a).total,mul_one])
      _ = 1 := μ.total

theorem sigma_moment (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) (f : Sigma β → ℚ) :
    (∑ z, (μ.sigma κ).weight z*f z)=
      ∑ a, μ.weight a*∑ b, (κ a).weight b*f ⟨a,b⟩ := by
  rw [Fintype.sum_sigma]
  simp only [sigma,mul_sum,mul_assoc]

end MetricKMedian.RationalLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) :
    SparseIntegerLaw β where
  length := ∑ a, (κ a).length
  states := Vector.ofFn (fun i => let z := finSigmaFinEquiv.symm i;
    (κ z.1).states[z.2.val])
  law := (μ.law.rational.sigma (fun a => (κ a).law.rational)).integer.reindex finSigmaFinEquiv

theorem bindIndexed_moment (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℚ) :
    (μ.bindIndexed κ).moment f=∑ a, μ.law.rational.weight a*(κ a).moment f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  have h := ρ.integer.reindex_moment finSigmaFinEquiv
    (fun z => f (κ z.1).states[z.2.val])
  have h' := μ.law.rational.sigma_moment (fun a => (κ a).law.rational)
    (fun z => f (κ z.1).states[z.2.val])
  simp only [RationalLaw.integer_weight] at h
  unfold moment bindIndexed
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1

theorem bindIndexed_property (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (P : β → Prop) (hP : ∀ a, ∀ b : Fin (κ a).length, P (κ a).states[b.val]) :
    ∀ i : Fin (μ.bindIndexed κ).length, P (μ.bindIndexed κ).states[i.val] := by
  intro i
  change P ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
    (κ z.1).states[z.2.val]))[i.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

theorem bindIndexed_length (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (M : ℕ) (hM : ∀ a, (κ a).length ≤ M) : (μ.bindIndexed κ).length ≤ μ.length*M := by
  change (∑ a, (κ a).length) ≤ _
  calc
    _ ≤ ∑ _a : Fin μ.length, M := sum_le_sum (fun a _ => hM a)
    _ = _ := by simp

def bindCompress {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) : SparseIntegerLaw β :=
  (μ.bindIndexed κ).compressAuto v

theorem bindCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) :
    let ν := μ.bindCompress κ v
    ν.length ≤ d+1 ∧
    (∀ i : Fin ν.length, ∃ a : Fin μ.length, ∃ b : Fin (κ a).length,
      ν.states[i.val]=(κ a).states[b.val]) ∧
    ∀ j, ν.moment (fun z => v z j)=
      ∑ a, μ.law.rational.weight a*(κ a).moment (fun z => v z j) := by
  have h := (μ.bindIndexed κ).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (bindIndexed_moment μ κ _)⟩
  intro i
  obtain ⟨b,hb⟩ := h.2.1 i
  let z := (finSigmaFinEquiv (n := fun a => (κ a).length)).symm b
  refine ⟨z.1,z.2,?_⟩
  exact hb.trans (by
    simp only [bindIndexed,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw

end OAI
