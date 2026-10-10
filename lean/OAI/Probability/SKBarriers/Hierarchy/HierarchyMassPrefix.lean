import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockSiteEmbedding
import OAI.Probability.SKBarriers.Scalar.TerminalPathStability

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem massFromAtoms_hierarchyAtom (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (i : Fin n) :
    massFromAtoms n (hierarchyAtom n m u) i=m i := by
  induction n generalizing u with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [massFromAtoms_last]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact hierarchyAtom_sum n _ _
    · rw [massFromAtoms_castSucc]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact ih _ _ j

def zeroInitialAtoms (k : ℕ) (m : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  hierarchyAtom k (fun i => m i.succ) 1

theorem zeroInitialAtoms_prefix (k : ℕ) (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (b : Fin (k+1)) : (∑ l, if l<b then zeroInitialAtoms k m l else 0)=m b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · simpa using hm.symm
  · simpa only [massFromAtoms,zeroInitialAtoms,Fin.lt_def,Fin.val_succ,Nat.lt_add_one_iff] using
      massFromAtoms_hierarchyAtom k (fun i => m i.succ) 1 i

theorem siteBlockMass_zeroInitial {k r : ℕ} (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (j : Fin ((k+1)*r)) : siteBlockMass r k (zeroInitialAtoms k m) j=m (finProdFinEquiv.symm j).1 :=
  zeroInitialAtoms_prefix k m hm _

theorem zeroInitialAtoms_nonneg {k : ℕ} (m : Fin (k+1) → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (k+1)) :
    0≤zeroInitialAtoms k m j :=
  hierarchyAtom_nonneg k _ (by norm_num) (fun i => (hm i.succ).1)
    (fun i => (hm i.succ).2) (fun _ _ h => hmono (Fin.succ_le_succ_iff.mpr h)) j

theorem zeroInitialAtoms_sum {k : ℕ} (m : Fin (k+1) → ℝ) :
    ∑ j, zeroInitialAtoms k m j=1 := hierarchyAtom_sum k _ 1

end SK.Analytic

end
end

end OAI
