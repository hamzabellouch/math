import OAI.Probability.InvariantIsing.Cavity.CavityProjectionGeometry

namespace OAI

/-! Correcting a spectral row sign sends an orthogonal matrix to SO
without changing its spectral compression blocks. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityOrientationSign {N : ℕ} (hN : 0 < N) (U : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => if i = (⟨0, hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)

lemma cavityOrientationSign_square {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    cavityOrientationSign hN U * (cavityOrientationSign hN U).transpose = 1 := by
  rw [cavityOrientationSign, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs
    · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> norm_num
    · norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

lemma cavityOrientationSign_det {N : ℕ} (hN : 0 < N) (U : Orthogonal N) :
    (cavityOrientationSign hN U).det = (U : Matrix (Fin N) (Fin N) ℝ).det := by
  simp [cavityOrientationSign, Matrix.det_diagonal]

def cavityOrientationLift {N : ℕ} (hN : 0 < N) (U : Orthogonal N) : SpecialOrthogonal N :=
  ⟨cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ), by
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
      rw [Matrix.transpose_mul]
      calc
        _ = cavityOrientationSign hN U *
            ((U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ).transpose) *
              (cavityOrientationSign hN U).transpose := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [(Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp U.property]
          simpa only [Matrix.mul_one] using cavityOrientationSign_square hN U
    · rw [Matrix.det_mul, cavityOrientationSign_det]
      rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> norm_num⟩

lemma measurable_cavityOrientationLift {N : ℕ} (hN : 0 < N) :
    Measurable (cavityOrientationLift hN) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun U : Orthogonal N =>
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) i j)
  simp only [cavityOrientationSign, Matrix.diagonal_mul]
  by_cases hi : i = (⟨0, hN⟩ : Fin N)
  · simp only [ite_eq_left hi]
    exact (continuous_subtype_val.matrix_det.measurable).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe))
  · simp only [ite_eq_right hi, one_mul]
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)

lemma cavityOrientationLift_right {N : ℕ} (hN : 0 < N)
    (U : Orthogonal N) (V : SpecialOrthogonal N) :
    cavityOrientationLift hN (U * cavitySpecialOrthogonal V) = cavityOrientationLift hN U * V := by
  apply Subtype.ext
  have hd : ((cavitySpecialOrthogonal V : Orthogonal N) : Matrix (Fin N) (Fin N) ℝ).det = 1 :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp V.property).2
  have hs : cavityOrientationSign hN (U * cavitySpecialOrthogonal V) = cavityOrientationSign hN U := by
    simp only [cavityOrientationSign, Submonoid.coe_mul, Matrix.det_mul, hd, mul_one]
  change cavityOrientationSign hN (U * cavitySpecialOrthogonal V) *
    ((U : Matrix (Fin N) (Fin N) ℝ) * (V : Matrix (Fin N) (Fin N) ℝ)) =
    (cavityOrientationSign hN U * (U : Matrix (Fin N) (Fin N) ℝ)) * (V : Matrix (Fin N) (Fin N) ℝ)
  rw [hs, Matrix.mul_assoc]

lemma cavityOrientationLift_compression {N n m : ℕ} (hN : 0 < N + n)
    (g : Fin (N + n) → Fin m) (U : Orthogonal (N + n)) :
    cavityCompressionGrams g (cavitySpecialOrthogonal (cavityOrientationLift hN U)) =
      cavityCompressionGrams g U := by
  funext a
  ext i j
  change (∑ k : Fin (N + n),
    (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N i) else 0) *
      (if g k = a then (cavityOrientationSign hN U * (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)) k (Fin.natAdd N j) else 0)) =
    ∑ k : Fin (N + n), (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N i) else 0) *
      (if g k = a then (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) k (Fin.natAdd N j) else 0)
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : g k = a
  · simp only [hk, ite_true, cavityOrientationSign, Matrix.diagonal_mul]
    split_ifs
    · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
    · ring
  · simp only [hk, ite_false, mul_zero]

lemma cavityOrientationLift_measure_rightInvariant {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [μ.IsMulRightInvariant] :
    (μ.map (cavityOrientationLift hN)).IsMulRightInvariant := by
  constructor
  intro V
  rw [Measure.map_map (measurable_mul_const V) (measurable_cavityOrientationLift hN)]
  have he : (fun S : SpecialOrthogonal N => S * V) ∘ cavityOrientationLift hN =
      cavityOrientationLift hN ∘ (fun U => U * cavitySpecialOrthogonal V) := by
    funext U
    exact (cavityOrientationLift_right hN U V).symm
  rw [he, ← Measure.map_map (measurable_cavityOrientationLift hN)
    (measurable_mul_const (cavitySpecialOrthogonal V)), map_mul_right_eq_self]

lemma cavityOrientationLift_compression_event {N n m : ℕ} (hN : 0 < N + n)
    (g : Fin (N + n) → Fin m) (μ : Measure (Orthogonal (N + n))) (L : ℝ) :
    (μ.map (cavityOrientationLift hN)).real {U | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} =
    μ.real {U | ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g U a))⁻¹‖ ≤ L} := by
  have hO : Measurable (cavitySpecialOrthogonal (N := N + n)) :=
    measurable_subtype_coe.subtype_mk
  have hs : MeasurableSet {U : SpecialOrthogonal (N + n) | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} := by
    have he : {U : SpecialOrthogonal (N + n) | ∀ a,
        ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} =
        ⋂ a, {U : SpecialOrthogonal (N + n) |
          ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L} := by
      ext U
      simp
    rw [he]
    apply MeasurableSet.iInter
    intro a
    apply measurableSet_le _ measurable_const
    exact ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      ((measurable_pi_apply a).comp ((measurable_cavityCompressionGrams g).comp hO))
  simp only [Measure.real, Measure.map_apply (measurable_cavityOrientationLift hN) hs]
  congr 2
  ext U
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, cavityOrientationLift_compression]

end InvariantIsing

end

end OAI
