import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRotation
import OAI.Probability.InvariantIsing.Cavity.CavityConditioning
import OAI.Probability.InvariantIsing.Cavity.CavityFrameOrbit

namespace OAI

/-! The finite conditioned Gaussian construction is an orthonormal frame
and has an exactly orthogonally invariant law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityArrayMatrix (n q : ℕ) :
    Measurable (cavityArrayMatrix n q) := by
  unfold cavityArrayMatrix
  fun_prop

def cavityArrayGood (n q : ℕ) : Set (EuclideanSpace ℝ (Fin n × Fin q)) :=
  {z | 0 < ((cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z).det}

lemma measurableSet_cavityArrayGood (n q : ℕ) : MeasurableSet (cavityArrayGood n q) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
      (cavityArrayMatrix n q z).transpose * cavityArrayMatrix n q z) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cavityArrayMatrix]
    fun_prop
  exact measurableSet_lt measurable_const hc.matrix_det.measurable

lemma cavityArrayGood_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityColumnRotation q (matrixRotation U)) ⁻¹' cavityArrayGood n q =
      cavityArrayGood n q := by
  ext z
  simp only [Set.mem_preimage, cavityArrayGood, Set.mem_ofPred_eq, cavityArrayMatrix_rotation,
    cavityGram_left_orthogonal _ _
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.property)]

lemma cavityArrayGood_probability (n q : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) =
      cavityGaussianRows q (cavityGoodGram q n) := by
  rw [← (cavityGaussianRows_finite_standard_law n q).map_eq,
    Measure.map_apply_of_aemeasurable (cavityGaussianRows_finite_standard_law n q).aemeasurable
      (measurableSet_cavityArrayGood n q)]
  congr 1
  ext x
  change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
  rw [cavityGaussianMatrix_gram]
  rfl

def cavityConditionedFrameLaw (n q : ℕ) : Measure (Matrix (Fin n) (Fin q) ℝ) :=
  (cond (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityArrayGood n q)).map
    (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z))

lemma cavityConditionedFrameLaw_of_rows (n q : ℕ) :
    (cond (cavityGaussianRows q) (cavityGoodGram q n)).map
      (fun x => cavityNormalizeFrame (cavityGaussianMatrix x n)) =
        cavityConditionedFrameLaw n q := by
  let f := fun x : ℕ → Fin q → ℝ => (WithLp.toLp 2
    (fun p : Fin n × Fin q => x p.1 p.2) : EuclideanSpace ℝ (Fin n × Fin q))
  have hf : Measurable f := (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr (fun p =>
      (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ))))
  have hpre : f ⁻¹' cavityArrayGood n q = cavityGoodGram q n := by
    ext x
    change 0 < ((cavityGaussianMatrix x n).transpose * cavityGaussianMatrix x n).det ↔ _
    rw [cavityGaussianMatrix_gram]
    rfl
  have hmap := cavity_conditioning_map (cavityGaussianRows q) f hf
    (cavityArrayGood n q) (measurableSet_cavityArrayGood n q)
  rw [hpre, (cavityGaussianRows_finite_standard_law n q).map_eq] at hmap
  rw [cavityConditionedFrameLaw, ← hmap]
  rw [Measure.map_map (show Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)) from
      (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)) hf]
  rfl

lemma cavityConditionedFrameLaw_probability {n q : ℕ}
    (hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0) :
    IsProbabilityMeasure (cavityConditionedFrameLaw n q) := by
  let := cond_isProbabilityMeasure hp
  unfold cavityConditionedFrameLaw
  infer_instance

theorem cavityConditionedFrameLaw_rotation {n q : ℕ} (U : Orthogonal n) :
    (cavityConditionedFrameLaw n q).map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) =
      cavityConditionedFrameLaw n q := by
  let f := fun z : EuclideanSpace ℝ (Fin n × Fin q) =>
    cavityNormalizeFrame (cavityArrayMatrix n q z)
  let act := fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A
  let R := cavityColumnRotation q (matrixRotation U)
  have hf : Measurable f := (measurable_cavityNormalizeFrame n q).comp
    (measurable_cavityArrayMatrix n q)
  have ha : Measurable act :=
    ((continuous_cavityFrameAction n q).comp (continuous_const.prodMk continuous_id)).measurable
  have hR : Measurable R := R.continuous.measurable
  have he : act ∘ f = f ∘ R := funext (fun z => (cavityArrayFrame_rotation U z).symm)
  have hinv := cavity_conditioning_invariant (stdGaussian _) R hR
    (cavityColumnRotation_gaussian (matrixRotation U)) (cavityArrayGood n q)
    (measurableSet_cavityArrayGood n q) (cavityArrayGood_rotation U)
  change ((cond (stdGaussian _) (cavityArrayGood n q)).map f).map act =
    (cond (stdGaussian _) (cavityArrayGood n q)).map f
  rw [Measure.map_map ha hf, he, ← Measure.map_map hf hR, hinv]

theorem cavityConditionedFrameLaw_orthonormal (n q : ℕ) :
    ∀ᵐ A ∂cavityConditionedFrameLaw n q, A.transpose * A = 1 := by
  have hf : Measurable (fun z => cavityNormalizeFrame (cavityArrayMatrix n q z)) :=
    (measurable_cavityNormalizeFrame n q).comp (measurable_cavityArrayMatrix n q)
  have hs : MeasurableSet {A : Matrix (Fin n) (Fin q) ℝ | A.transpose * A = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
      continuous_const).measurableSet
  rw [cavityConditionedFrameLaw, ae_map_iff hf.aemeasurable hs]
  apply ae_cond_of_forall_mem (measurableSet_cavityArrayGood n q)
  intro z hz
  apply cavityNormalizeFrame_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self (cavityArrayMatrix n q z)
  · exact ne_of_gt hz

theorem cavityConditionedFrameLaw_eventually_probability (q : ℕ) :
    ∀ᶠ n in Filter.atTop, IsProbabilityMeasure (cavityConditionedFrameLaw n q) := by
  filter_upwards [cavityGoodGram_eventually_positive q] with n hn
  have hp : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability]
    exact fun h => by simp [Measure.real, h] at hn
  exact cavityConditionedFrameLaw_probability hp

end InvariantIsing

end

end OAI
