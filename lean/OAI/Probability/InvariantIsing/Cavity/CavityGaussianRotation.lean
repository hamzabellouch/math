import OAI.Probability.InvariantIsing.Cavity.CavityFrameRotation
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGaussian
import OAI.Probability.InvariantIsing.Cavity.CavityFrameMeasurable
import OAI.Probability.InvariantIsing.Haar.MatrixRotation

namespace OAI

/-! Orthogonal invariance of the finite Gaussian array, expressed as a
simultaneous rotation of all its columns. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InvariantIsing

def cavityColumnEquiv (n q : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin q) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin q => EuclideanSpace ℝ (Fin n)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((Equiv.prodComm (Fin n) (Fin q)).trans (Equiv.sigmaEquivProd (Fin q) (Fin n)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin q) (_ : Fin n) => ℝ))

@[simp] lemma cavityColumnEquiv_apply {n q : ℕ}
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (j : Fin q) (k : Fin n) :
    cavityColumnEquiv n q x j k = x (k, j) := rfl

@[simp] lemma cavityColumnEquiv_symm_apply {n q : ℕ}
    (x : PiLp 2 (fun _ : Fin q => EuclideanSpace ℝ (Fin n))) (k : Fin n) (j : Fin q) :
    (cavityColumnEquiv n q).symm x (k, j) = x j k := rfl

def cavityColumnRotation {n : ℕ} (q : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n × Fin q) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin q) :=
  ((cavityColumnEquiv n q).trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => U))).trans
    (cavityColumnEquiv n q).symm

lemma cavityColumnRotation_apply {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n × Fin q)) (k : Fin n) (j : Fin q) :
    cavityColumnRotation q U x (k, j) =
      U (WithLp.toLp 2 (fun i : Fin n => x (i, j))) k := rfl

theorem cavityColumnRotation_gaussian {n q : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map (cavityColumnRotation q U) =
      stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) :=
  stdGaussian_map (cavityColumnRotation q U)

def cavityArrayMatrix (n q : ℕ) (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    Matrix (Fin n) (Fin q) ℝ := fun k j => z (k, j) / Real.sqrt n

lemma cavityArrayMatrix_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityArrayMatrix n q z := by
  ext k j
  simp only [cavityArrayMatrix, cavityColumnRotation_apply, matrixRotation_apply,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

lemma cavityArrayFrame_rotation {n q : ℕ} (U : Orthogonal n)
    (z : EuclideanSpace ℝ (Fin n × Fin q)) :
    cavityNormalizeFrame (cavityArrayMatrix n q (cavityColumnRotation q (matrixRotation U) z)) =
      (U : Matrix (Fin n) (Fin n) ℝ) * cavityNormalizeFrame (cavityArrayMatrix n q z) := by
  rw [cavityArrayMatrix_rotation]
  exact cavityNormalizeFrame_left_orthogonal _ _
    ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)

def cavityFrameLaw (n q : ℕ) : Measure (Matrix (Fin n) (Fin q) ℝ) :=
  (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map
    (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z))

/-- The finite Gaussian construction is exactly invariant under rotations
of the ambient space, before passing to the large-dimension limit. -/
theorem cavityFrameLaw_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityFrameLaw n q).map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) =
      cavityFrameLaw n q := by
  let f := fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)
  let act := fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A
  let R := cavityColumnRotation q (matrixRotation U)
  have hf : Measurable f := (measurable_cavityNormalizeFrame n q).comp (by
    unfold cavityArrayMatrix
    fun_prop)
  have ha : Measurable act := by
    apply Measurable.of_eval_matrix
    intro i j
    change Measurable (fun A : Matrix (Fin n) (Fin q) ℝ => ∑ k, (U : Matrix _ _ ℝ) i k * A k j)
    exact Finset.measurable_sum _ (fun k _ =>
      (Matrix.measurable_apply (i := k) (j := j)).const_mul _)
  have hR : Measurable R := R.continuous.measurable
  have he : act ∘ f = f ∘ R := by
    funext z
    exact (cavityArrayFrame_rotation U z).symm
  change ((stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map f).map act =
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))).map f
  rw [Measure.map_map ha hf, he, ← Measure.map_map hf hR,
    cavityColumnRotation_gaussian]

end InvariantIsing

end

end OAI
