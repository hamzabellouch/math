import OAI.Geometry.RuledCovering.Projection

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

abbrev Coordinates := Fin 2 → ℝ

def frameJacobian (M : Coordinates ≃L[ℝ] Plane) : ℝ :=
  |(M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toContinuousLinearMap.det|

lemma frameJacobian_pos (M : Coordinates ≃L[ℝ] Plane) : 0 < frameJacobian M := by
  apply abs_pos.mpr
  exact (M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toLinearEquiv.isUnit_det'.ne_zero

lemma frame_integral_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) (F : Plane → ℝ) :
    (∫ p in M '' K, F p) = frameJacobian M * (∫ x in K, F (M x)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℝ
  let D := M.trans e
  have himage : M '' K = e.symm '' (D '' K) := by
    rw [← image_comp]
    congr 1

  rw [himage]
  have hmp : MeasurePreserving e.symm volume volume := PiLp.volume_preserving_toLp (Fin 2)
  rw [hmp.setIntegral_image_emb e.symm.toHomeomorph.measurableEmbedding]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK
    (fun x _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn]
  rw [integral_smul]
  rfl

lemma frame_volume_image (M : Coordinates ≃L[ℝ] Plane) {K : Set Coordinates}
    (hK : MeasurableSet K) : volume.real (M '' K) = frameJacobian M * volume.real K := by
  simpa using frame_integral_image M hK (fun _ => (1 : ℝ))

lemma coordinates_closedBall (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    closedBall b a = Set.pi univ (fun i => Icc (b i - a) (b i + a)) := by
  ext x
  simp only [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha, Real.norm_eq_abs,
    Pi.sub_apply, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith

lemma coordinates_closedBall_volume (b : Coordinates) {a : ℝ} (ha : 0 ≤ a) :
    volume.real (closedBall b a) = (2 * a) ^ 2 := by
  rw [coordinates_closedBall b ha, measureReal_def, volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_sub_cancel, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ a + a)]
  ring

lemma coordinates_closedBall_parallelogram (b : Coordinates) {a : ℝ} (ha : 0 < a) :
    IsParallelogram (closedBall b a) := by
  let u : Coordinates := ![2*a, 0]
  let v : Coordinates := ![0, 2*a]
  refine ⟨![b 0 - a, b 1 - a], u, v, ?_, ?_⟩
  · have heq : (![u, v] : Fin 2 → Coordinates) =
        fun i => (2 * a) • Pi.basisFun ℝ (Fin 2) i := by
      funext i
      ext j
      fin_cases i <;> fin_cases j <;> simp [u, v, Pi.basisFun_apply]
    rw [heq]
    exact (Pi.basisFun ℝ (Fin 2)).linearIndependent.units_smul
      (fun _ => Units.mk0 (2 * a) (by positivity))
  · rw [coordinates_closedBall b ha.le]
    ext x
    simp only [Set.mem_pi, mem_univ, true_implies, mem_Icc, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨(x 0 - (b 0 - a)) / (2*a), ?_, (x 1 - (b 1 - a)) / (2*a), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 0).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 0).2]
      · constructor
        · exact div_nonneg (sub_nonneg.mpr (hx 1).1) (by positivity)
        · apply (div_le_one (by positivity)).mpr
          linarith [(hx 1).2]
      · ext i
        fin_cases i <;> simp [u, v, (by positivity : 2*a ≠ 0)]
    · rintro ⟨s, hs, t, ht, rfl⟩ i
      fin_cases i <;> simp [u, v] <;> constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

end RuledApproximation

end

end OAI
