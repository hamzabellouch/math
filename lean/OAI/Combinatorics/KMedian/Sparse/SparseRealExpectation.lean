import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Sparse.SparseMap
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Sparse.SparseBind

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

noncomputable def expectation (μ : SparseIntegerLaw α) (f : α → ℝ) : ℝ :=
  μ.realIndex.expect (fun i => f μ.states[i.val])

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_const (μ : SparseIntegerLaw α) (c : ℝ) :
    μ.expectation (fun _ => c)=c := μ.realIndex.expect_const c

theorem expectation_add (μ : SparseIntegerLaw α) (f g : α → ℝ) :
    μ.expectation (fun a => f a+g a)=μ.expectation f+μ.expectation g :=
  μ.realIndex.expect_add _ _

theorem expectation_mono (μ : SparseIntegerLaw α) (f g : α → ℝ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val] ≤ g μ.states[i.val]) :
    μ.expectation f ≤ μ.expectation g := by
  simp only [expectation_def]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (by exact_mod_cast μ.law.rational.nonneg i)

theorem expectation_bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℝ) :
    (μ.bindIndexed κ).expectation f=
      ∑ a, (μ.law.rational.weight a:ℝ)*(κ a).expectation f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  calc
    _ = ∑ z, (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val] := by
      unfold expectation realIndex
      change (∑ i, (((ρ.integer.reindex finSigmaFinEquiv).rational.weight i):ℝ)*
        f ((Vector.ofFn (fun j => let z := finSigmaFinEquiv.symm j;
          (κ z.1).states[z.2.val]))[i.val])) = _
      simp only [Vector.getElem_ofFn]
      change (∑ i, (ρ.integer.rational.weight (finSigmaFinEquiv.symm i):ℝ)*
        f (κ (finSigmaFinEquiv.symm i).1).states[(finSigmaFinEquiv.symm i).2.val]) = _
      simp only [RationalLaw.integer_weight]
      exact (finSigmaFinEquiv (n := fun a => (κ a).length)).symm.sum_comp
        (fun z : Sigma (fun a : Fin μ.length => Fin (κ a).length) =>
          (ρ.weight z:ℝ)*f (κ z.1).states[z.2.val])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [ρ,RationalLaw.sigma,Rat.cast_mul,mul_assoc,← mul_sum,expectation_def]

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

theorem expectation_dirac (a : α) (f : α → ℝ) :
    (dirac a).expectation f=f a := by
  simp only [expectation_def,dirac,IntegerLaw.rational]
  norm_num

end MetricKMedian.SparseIntegerLaw

end OAI
