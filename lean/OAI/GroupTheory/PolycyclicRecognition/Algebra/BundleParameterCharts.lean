import OAI.GroupTheory.PolycyclicRecognition.Algebra.BundleWordCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # The actual global interval coordinates, grouped into source bundles -/

noncomputable section
namespace PolycyclicRecognition

/-- A coordinate permutation followed by currying. -/
def rectangularCoordinateChart {h n M : ℕ} (e : Fin h × Fin n ≃ Fin M) :
    (Fin M → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun t i j => t (e (i, j))
      invFun := fun t k => t (e.symm k).1 (e.symm k).2
      left_inv := by intro t; funext k; simp
      right_inv := by intro t; funext i j; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem rectangularCoordinateChart_apply {h n M : ℕ} (e : Fin h × Fin n ≃ Fin M)
    (t : Fin M → ℝ) (i : Fin h) (j : Fin n) :
    rectangularCoordinateChart e t i j = t (e (i, j)) := rfl

/-- First all first samples, then all second samples; each block is grouped
by bundle before the generator position. -/
def bundleParameterIndex (h m : ℕ) :
    Fin h × Fin (m + m) ≃ Fin (h * m + h * m) :=
  (Equiv.prodCongr (Equiv.refl (Fin h)) finSumFinEquiv.symm).trans
    ((Equiv.prodSumDistrib (Fin h) (Fin m) (Fin m)).trans
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv))

def bundleParameterChart (h m : ℕ) :
    (Fin (h * m + h * m) → ℝ) ≃L[ℝ] (Fin h → Fin (m + m) → ℝ) :=
  rectangularCoordinateChart (bundleParameterIndex h m)

def bundleOutputChart (h n : ℕ) :
    (Fin (h * n) → ℝ) ≃L[ℝ] (Fin h → Fin n → ℝ) :=
  rectangularCoordinateChart finProdFinEquiv

theorem bundleParameterIndex_left (h m : ℕ) (i : Fin h) (j : Fin m) :
    bundleParameterIndex h m (i, Fin.castAdd m j) =
      Fin.castAdd (h * m) (finProdFinEquiv (i, j)) := by
  simp only [bundleParameterIndex, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.prodSumDistrib_apply_left, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

theorem bundleParameterIndex_right (h m : ℕ) (i : Fin h) (j : Fin m) :
    bundleParameterIndex h m (i, Fin.natAdd m j) =
      Fin.natAdd (h * m) (finProdFinEquiv (i, j)) := by
  simp only [bundleParameterIndex, Equiv.trans_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.prodSumDistrib_apply_right, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem bundleParameterChart_left (h m : ℕ) (t : Fin (h * m + h * m) → ℝ)
    (i : Fin h) (j : Fin m) :
    bundleParameterChart h m t i (Fin.castAdd m j) =
      t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) := by
  simp [bundleParameterChart, bundleParameterIndex]

theorem bundleParameterChart_right (h m : ℕ) (t : Fin (h * m + h * m) → ℝ)
    (i : Fin h) (j : Fin m) :
    bundleParameterChart h m t i (Fin.natAdd m j) =
      t (Fin.natAdd (h * m) (finProdFinEquiv (i, j))) := by
  simp only [bundleParameterChart, rectangularCoordinateChart_apply, bundleParameterIndex,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.prodSumDistrib_apply_right,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

end PolycyclicRecognition

end

end OAI
