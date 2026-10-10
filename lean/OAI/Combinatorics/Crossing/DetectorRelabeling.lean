import OAI.Combinatorics.Crossing.RankDetector
import Mathlib.Data.Finset.Sort

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem nodePolynomial_equiv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (node : ι → ℝ) (e : κ ≃ ι) :
    nodePolynomial (node ∘ e) = nodePolynomial node := by
  exact e.prod_comp (fun i => Polynomial.X-Polynomial.C (node i))

theorem derivativeAtNode_equiv (node : ι → ℝ) (e : κ ≃ ι) (p : κ) :
    derivativeAtNode (node ∘ e) p = derivativeAtNode node (e p) := by
  simp only [derivativeAtNode, nodePolynomial_equiv, Function.comp_apply]

theorem detectorAtom_equiv (s : ℕ) (node : ι → ℝ) (e : κ ≃ ι) (p q : κ) :
    detectorAtom s (node ∘ e) p q = detectorAtom s node (e p) (e q) := by
  unfold detectorAtom detectorWeight
  rw [derivativeAtNode_equiv, derivativeAtNode_equiv]
  rfl

theorem rankDetector_equiv (s : ℕ) (node : ι → ℝ) (e : κ ≃ ι) (H : Matrix ι ι ℝ) :
    rankDetector s (node ∘ e) (H.submatrix e e) = rankDetector s node H := by
  change (∑ p, ∑ q, H (e p) (e q) • detectorAtom s (node ∘ e) p q) = _
  simp only [detectorAtom_equiv]
  calc
    _ = ∑ p : κ, ∑ q : ι, H (e p) q • detectorAtom s node (e p) q := by
      apply Finset.sum_congr rfl
      intro p hp
      exact e.sum_comp (fun q => H (e p) q • detectorAtom s node (e p) q)
    _ = _ := e.sum_comp (fun p => ∑ q, H p q • detectorAtom s node p q)

def halfOrderMatrix (α : Type*) [LinearOrder α] : Matrix α α ℝ :=
  fun p q => if p < q then (1/2 : ℝ) else if q < p then -1/2 else 0

theorem halfOrderMatrix_orderIso
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [LinearOrder ι] [LinearOrder κ] (e : κ ≃o ι) :
    (halfOrderMatrix ι).submatrix e e = halfOrderMatrix κ := by
  funext p q
  simp [halfOrderMatrix]

end Zarankiewicz

end

end OAI
