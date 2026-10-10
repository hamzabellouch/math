import OAI.Probability.InvariantIsing.Cavity.CavityCascadeSpectralLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGroupCovariancePositive

namespace OAI

/-! Positivity of finite cascade covariance paths with a prescribed
diagonal and an independent terminal residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma cavity_cascade_patch_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (h0 : 0 ≤ a 0) {D : ℝ} (hD : a n ≤ D) (σ : ℕ → LabeledLeaf n) :
    GramDiagonal D (diagonalPatch D (cascadeScalarArray n a σ)) := by
  constructor
  · intro r
    let A : Fin r → ℕ →₀ ℝ := fun i =>
      treeFieldCoefficients n (σ i) (fun j => pathAmplitude a j) (fun _ : Unit => 1)
    have hA (i j : Fin r) : cylinderCross (A i) (A j) = cascadeScalarArray n a σ i j := by
      rw [treeField_path_cross n (σ i) (σ j) ha h0]
      simp only [Fintype.sum_unique, mul_one, cascadeScalarArray]
    have hM : (fun i j : Fin r => diagonalPatch D (cascadeScalarArray n a σ) i j) =
        (show Matrix (Fin r) (Fin r) ℝ from fun i j => cylinderCross (A i) (A j)) +
          Matrix.diagonal (fun _ => D - a n) := by
      funext i j
      change (if (i : ℕ) = (j : ℕ) then D else cascadeScalarArray n a σ i j) =
        cylinderCross (A i) (A j) + (if i = j then D - a n else 0)
      simp only [hA, Fin.val_inj]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, cascadeScalarArray, labeledCommonDepth_self]
        ring
      · simp only [ite_eq_right hij, add_zero]
    rw [hM]
    exact (cylinderCross_matrix_posSemidef A).add
      (Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr hD))
  · intro i
    simp only [diagonalPatch, ite_true]

lemma cavity_cascade_transformed_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (f : ℝ → ℝ) (hf : Monotone f) (hf0 : 0 ≤ f (a 0)) {D : ℝ} (hfD : f (a n) ≤ D)
    (σ : ℕ → LabeledLeaf n) (r : ℕ) :
    Matrix.PosSemidef (fun i j : Fin r =>
      if i = j then D else f (cascadeScalarArray n a σ i j)) := by
  have h := (cavity_cascade_patch_gram n (hf.comp ha) hf0 hfD σ).1 r
  simpa only [diagonalPatch, cascadeScalarArray, Function.comp_apply, Fin.val_inj] using h

end InvariantIsing

end

end OAI
