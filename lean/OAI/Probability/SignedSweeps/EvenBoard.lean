import OAI.Probability.SignedSweeps.SweepBlockLayers
import OAI.Probability.SignedSweeps.SpectralConj
import OAI.Probability.SignedSweeps.EvenMean

namespace OAI

noncomputable section
namespace SignedSweeps.EvenColorDensity
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenBoardTensorFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) evenBoardTensorSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {C : Type} [Fintype C]

lemma tensor_conjugate (p : ℕ) (R : EvenColorDensity C) :
    R.tensor p = isometricConj (wordTensorBasis (C ⊕ C) p).repr
      (tensorOperator (colorHilbert (C ⊕ C)) (fun _ : Fin p => R.matrix.toEuclideanLin)) :=
  varyingWordTensor_conjugate (fun _ : Fin p => R.matrix)

lemma tensor_positive (p : ℕ) (R : EvenColorDensity C) : (R.tensor p).IsPositive := by
  rw [tensor_conjugate]
  exact isometricConj_positive _ (tensorOperator_positive _ _
    (fun _ => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive R)))

end SignedSweeps.EvenColorDensity
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) evenBoardDensityFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) evenBoardDensitySumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _
variable {A B C : Type} [Fintype A] [Fintype B] [Nonempty B] [Fintype C]

lemma word_density_right_support
    (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → EvenColorDensity C) :
    (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin *
      spectralSupport ((EvenColorDensity.mean R).tensor W.card)
        ((EvenColorDensity.mean R).tensor_positive W.card) =
      (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin := by
  have hh := tensor_density_right_support (colorHilbert (C ⊕ C)) W e
    (fun j => (R j).matrix.toEuclideanLin)
    (fun j => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (R j)))
  simp only [← EvenColorDensity.mean_linear] at hh
  apply_fun isometricConj (wordTensorBasis (C ⊕ C) W.card).repr at hh
  simp only [isometricConj_mul, ← spectralSupport_isometricConj,
    ← varyingWordTensor_conjugate] at hh
  exact hh

lemma word_density_cell_bound
    (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → EvenColorDensity C) (S : A → EvenColorDensity C) :
    ‖(positiveRoot (varyingWordTensor (fun k => (R (e k).1.2).matrix)).toEuclideanLin
        (Matrix.isPositive_toEuclideanLin_iff.mpr
          (varyingWordTensor_positive _ (fun k => evenColorMatrix_positive (R (e k).1.2)))) *
      supportInverseRoot ((EvenColorDensity.mean R).tensor W.card)
        ((EvenColorDensity.mean R).tensor_positive W.card) *
      positiveRoot (varyingWordTensor (fun k => (S (e k).1.1).matrix)).toEuclideanLin
        (Matrix.isPositive_toEuclideanLin_iff.mpr
          (varyingWordTensor_positive _ (fun k => evenColorMatrix_positive (S (e k).1.1))))).toContinuousLinearMap‖^2 ≤
      missingCellFactor W := by
  have hh := tensor_density_cell_bound (colorHilbert (C ⊕ C)) W e
    (fun j => (R j).matrix.toEuclideanLin)
    (fun j => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (R j)))
    (fun i => (S i).matrix.toEuclideanLin)
    (fun i => Matrix.isPositive_toEuclideanLin_iff.mpr (evenColorMatrix_positive (S i)))
    (fun i => (S i).matrix_trace_linear)
  simp only [← EvenColorDensity.mean_linear] at hh
  rw [← isometricConj_norm (wordTensorBasis (C ⊕ C) W.card).repr] at hh
  simp only [isometricConj_mul, ← positiveRoot_isometricConj,
    ← supportInverseRoot_isometricConj, ← varyingWordTensor_conjugate] at hh
  exact hh

end SignedSweeps
end

end OAI
