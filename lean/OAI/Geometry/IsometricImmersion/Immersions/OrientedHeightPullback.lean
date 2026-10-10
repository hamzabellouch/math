import OAI.Geometry.IsometricImmersion.Obstructions.LocalAdmissibility
import OAI.Geometry.IsometricImmersion.Calculus.AffineCovariantHessian
import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature
import OAI.Geometry.IsometricImmersion.Coordinates.OrientedPatchSquares
import OAI.Geometry.IsometricImmersion.Obstructions.PatchAdmissibility

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

def orientedCovHessian (g : MetricField) (z : Coord → ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  Rᵀ * covHessian g z p * R

theorem orientedCovHessian_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => orientedCovHessian g z R p i j) U := by
  simp only [orientedCovHessian, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.mul _ contDiffOn_const
  apply ContDiffOn.sum
  intro a _
  exact contDiffOn_const.mul (covHessian_contDiffOn hg hU hz a k)

theorem exists_open_oriented_height_neighborhood
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hb : b ∈ U) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : 0 < heightEnergy g z b) (hyy : orientedCovHessian g z R b 1 1 ≠ 0)
    (hq : |orientedCovHessian g z R b 0 1 / orientedCovHessian g z R b 1 1| <
      (1 : ℝ) / 100) :
    ∃ V : Set Coord, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧
      ∀ p ∈ V, 0 < heightEnergy g z p ∧ orientedCovHessian g z R p 1 1 ≠ 0 ∧
        |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1| <
          (1 : ℝ) / 100 := by
  have hEc : ContinuousAt (heightEnergy g z) b :=
    (heightEnergy_contDiffOn hg hU hz).continuousOn.continuousAt (hU.mem_nhds hb)
  have hHc (i j : Fin 2) : ContinuousAt (fun p => orientedCovHessian g z R p i j) b :=
    (orientedCovHessian_contDiffOn hg hz hU R i j).continuousOn.continuousAt (hU.mem_nhds hb)
  have hqc : ContinuousAt (fun p =>
      |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1|) b :=
    ((hHc 0 1).div (hHc 1 1) hyy).abs
  have hgood : {p | p ∈ U ∧ 0 < heightEnergy g z p ∧
      orientedCovHessian g z R p 1 1 ≠ 0 ∧
      |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1| <
        (1 : ℝ) / 100} ∈ 𝓝 b := by
    filter_upwards [hU.mem_nhds hb, continuousAt_const.eventually_lt hEc hE,
      (hHc 1 1).eventually_ne hyy, hqc.eventually_lt continuousAt_const hq]
      with p hp hEp hyyp hqp
    exact ⟨hp, hEp, hyyp, hqp⟩
  obtain ⟨V, hVsub, hVo, hbV⟩ := mem_nhds_iff.mp hgood
  exact ⟨V, hVo, hbV, fun p hp => (hVsub hp).1, fun p hp => (hVsub hp).2⟩

theorem rank_one_height_has_oriented_neighborhood
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hb : b ∈ U) (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) :
    ∃ R : OrientationLabel, ∃ V : Set Coord,
      IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧
      ∀ p ∈ V, 0 < heightEnergy g (height F e) p ∧
        orientedCovHessian g (height F e) R.val p 1 1 ≠ 0 ∧
        |orientedCovHessian g (height F e) R.val p 0 1 /
          orientedCovHessian g (height F e) R.val p 1 1| < (1 : ℝ) / 100 := by
  have hz := height_smooth hF.1 e
  have hnpoint := geometric_height_normal_point hF hU hb he
  have hsym : (covHessian g (height F e) b)ᵀ = covHessian g (height F e) b := by
    ext i j
    exact covHessian_symm hg hU hz hb j i
  have hHrank : (covHessian g (height F e) b).rank = 1 := by
    rw [hnpoint.2]
    exact hrank
  obtain ⟨R, hRnet, hRyy, hRq⟩ :=
    exists_orientationRotation_for_rank_one (covHessian g (height F e) b) hsym hHrank
  have hE : 0 < heightEnergy g (height F e) b := by
    rw [heightEnergy_at_critical g (height F e) b hnpoint.1]
    exact (hg.2 b hb).det_pos
  obtain ⟨V, hVo, hbV, hVU, hVgood⟩ :=
    exists_open_oriented_height_neighborhood hg hz hU hb R hE hRyy hRq
  exact ⟨⟨R, hRnet⟩, V, hVo, hbV, hVU, hVgood⟩

theorem scaled_matrix_congruence (H R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ) :
    (scale • R)ᵀ * H * (scale • R) = scale ^ 2 • (Rᵀ * H * R) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Fin.sum_univ_two, smul_eq_mul]
  ring

theorem affinePullbackMetric_scaled (g : MetricField) (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ) (p : Coord) :
    affinePullbackMetric g c (scale • R) p =
      scale ^ 2 • (Rᵀ * g (affineCoordinates c (scale • R) p) * R) :=
  scaled_matrix_congruence _ R scale

theorem covHessian_affinePullback_scaled
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ)
    (hM : IsUnit (scale • R)) (p : Coord) (hp : affineCoordinates c (scale • R) p ∈ U) :
    covHessian (affinePullbackMetric g c (scale • R)) (z ∘ affineCoordinates c (scale • R)) p =
      scale ^ 2 • orientedCovHessian g z R (affineCoordinates c (scale • R) p) := by
  rw [covHessian_affinePullback hg hz hU c (scale • R) hM p hp]
  exact scaled_matrix_congruence _ R scale

theorem heightEnergy_affinePullback_scaled
    {g : MetricField} {z : Coord → ℝ} (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hRdet : R.det = 1) (scale : ℝ) (hM : IsUnit (scale • R)) (p : Coord)
    (hz : DifferentiableAt ℝ z (affineCoordinates c (scale • R) p)) :
    heightEnergy (affinePullbackMetric g c (scale • R)) (z ∘ affineCoordinates c (scale • R)) p =
      scale ^ 4 * heightEnergy g z (affineCoordinates c (scale • R) p) := by
  rw [heightEnergy_affinePullback c (scale • R) hM p hz]
  simp only [Matrix.det_smul, Fintype.card_fin, hRdet, mul_one]
  ring

theorem gaussianCurvature_affinePullback_scaled
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ)
    (hM : IsUnit (scale • R)) (p : Coord) (hp : affineCoordinates c (scale • R) p ∈ U) :
    gaussianCurvature (affinePullbackMetric g c (scale • R)) p =
      gaussianCurvature g (affineCoordinates c (scale • R) p) :=
  gaussianCurvature_affinePullback hg hU c (scale • R) hM p hp

theorem modelSquare_subset_closedPatchBox : modelSquare ⊆ closedPatchBox := by
  intro p hp i
  have hpi : (-3 : ℝ) ≤ p i ∧ p i ≤ 3 := ⟨hp.1 i, hp.2 i⟩
  change (-4 : ℝ) ≤ p i ∧ p i ≤ 4
  constructor <;> linarith [hpi.1, hpi.2]

theorem oriented_patch_height_admissible_of_subset
    {g : MetricField} {F : Coord → Ambient} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (e : Ambient) (he : inner ℝ e e = 1) (hVU : V ⊆ U)
    (R : OrientationLabel)
    (hgood : ∀ q ∈ V, 0 < heightEnergy g (height F e) q ∧
      orientedCovHessian g (height F e) R.val q 1 1 ≠ 0 ∧
      |orientedCovHessian g (height F e) R.val q 0 1 /
        orientedCovHessian g (height F e) R.val q 1 1| < (1 : ℝ) / 100)
    (n k : ℕ) (c : Coord) (hpatch : orientedClosedPatch n k R c ⊆ V) :
    PatchAdmissibleHeight
      (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
      (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  let M := orientedPatchScale n k R • R.val
  let W := affineCoordinates c M ⁻¹' U
  let gP := affinePullbackMetric g c M
  let FP := affinePullbackImmersion F c M
  let zP := height FP e
  have hM : IsUnit M := orientedPatchMatrix_isUnit n k R
  have hW : IsOpen W := isOpen_affine_preimage hU c M
  have hSimage (p : Coord) (hp : p ∈ modelSquare) : affineCoordinates c M p ∈ V :=
    hpatch ⟨p, modelSquare_subset_closedPatchBox hp, rfl⟩
  have hSW : modelSquare ⊆ W := fun p hp => hVU (hSimage p hp)
  have hgP : SmoothPositiveOn gP W :=
    affinePullbackMetric_smoothPositive hg c M (Matrix.mulVec_injective_of_isUnit hM)
  have hFP : IsometricOn gP FP W := affinePullbackImmersion_isometric hF hU c M
  have hzP : ContDiffOn ℝ ∞ zP W := height_smooth hFP.1 e
  have hz : ContDiffOn ℝ ∞ (height F e) U := height_smooth hF.1 e
  have hscale : (orientedPatchScale n k R) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (orientedPatchScale_pos n k R).ne'
  have hpoint (p : Coord) (hp : p ∈ modelSquare) :
      0 < heightEnergy gP zP p ∧ covHessian gP zP p 1 1 ≠ 0 ∧
      |hessianQuotient gP zP p| ≤ (1 : ℝ) / 100 := by
    have hpU := hVU (hSimage p hp)
    have hpGood := hgood _ (hSimage p hp)
    have hH : covHessian gP zP p = (orientedPatchScale n k R) ^ 2 •
        orientedCovHessian g (height F e) R.val (affineCoordinates c M p) :=
      covHessian_affinePullback_scaled hg hz hU c R.val (orientedPatchScale n k R) hM p hpU
    refine ⟨?_, ?_, ?_⟩
    · change 0 < heightEnergy (affinePullbackMetric g c M)
        ((height F e) ∘ affineCoordinates c M) p
      apply (heightEnergy_affinePullback_pos_iff c M hM p
        (((hz _ hpU).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))).mpr
      exact hpGood.1
    · rw [hH]
      exact mul_ne_zero hscale hpGood.2.1
    · unfold hessianQuotient
      rw [hH]
      simp only [Matrix.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hscale]
      exact hpGood.2.2.le
  refine ⟨W, hW, hSW, hgP, hzP, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [heightEnergy, mul_assoc] using geometric_height_equation hgP hFP hW e he (hSW hp)
  · intro p hp; exact (hpoint p hp).1
  · intro p hp; exact (hpoint p hp).2.1
  · intro p hp; exact (hpoint p hp).2.2

end SmoothLocal.Geometry

end

end OAI
