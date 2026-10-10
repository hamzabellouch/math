import OAI.Geometry.IsometricImmersion.Calculus.AffineHessian
import OAI.Geometry.IsometricImmersion.Immersions.RankOneOrientation
import OAI.Geometry.IsometricImmersion.Curvature.NegativeCurvatureHeight
import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem exists_open_admissibility_neighborhood
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hE : 0 < heightEnergy g z p)
    (hyy : covHessian g z p 1 1 ≠ 0)
    (hq : |covHessian g z p 0 1 / covHessian g z p 1 1| < (1 / 100 : ℝ)) :
    ∃ V : Set Coord, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∀ q ∈ V, 0 < heightEnergy g z q ∧ covHessian g z q 1 1 ≠ 0 ∧
        |covHessian g z q 0 1 / covHessian g z q 1 1| < (1 / 100 : ℝ) := by
  have hEc : ContinuousAt (heightEnergy g z) p :=
    (heightEnergy_contDiffOn hg hU hz).continuousOn.continuousAt (hU.mem_nhds hp)
  have hHc (i j : Fin 2) : ContinuousAt (fun q => covHessian g z q i j) p :=
    (covHessian_contDiffOn hg hU hz i j).continuousOn.continuousAt (hU.mem_nhds hp)
  have hqc : ContinuousAt
      (fun q => |covHessian g z q 0 1 / covHessian g z q 1 1|) p :=
    ((hHc 0 1).div (hHc 1 1) hyy).abs
  have hgood : {q | q ∈ U ∧ 0 < heightEnergy g z q ∧
      covHessian g z q 1 1 ≠ 0 ∧
      |covHessian g z q 0 1 / covHessian g z q 1 1| < (1 / 100 : ℝ)} ∈ 𝓝 p := by
    filter_upwards [hU.mem_nhds hp,
      continuousAt_const.eventually_lt hEc hE,
      (hHc 1 1).eventually_ne hyy,
      hqc.eventually_lt continuousAt_const hq] with q hqU hqE hqyy hqq
    exact ⟨hqU, hqE, hqyy, hqq⟩
  obtain ⟨V, hVsub, hVo, hpV⟩ := mem_nhds_iff.mp hgood
  exact ⟨V, hVo, hpV, fun q hqV => (hVsub hqV).1,
    fun q hqV => (hVsub hqV).2⟩

theorem exists_open_admissibility_at_critical
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hcrit : fderiv ℝ z p = 0)
    (hyy : covHessian g z p 1 1 ≠ 0)
    (hq : |covHessian g z p 0 1 / covHessian g z p 1 1| < (1 / 100 : ℝ)) :
    ∃ V : Set Coord, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∀ q ∈ V, 0 < heightEnergy g z q ∧ covHessian g z q 1 1 ≠ 0 ∧
        |covHessian g z q 0 1 / covHessian g z q 1 1| < (1 / 100 : ℝ) := by
  apply exists_open_admissibility_neighborhood hg hz hU hp _ hyy hq
  rw [heightEnergy_at_critical g z p hcrit]
  exact (hg.2 p hp).det_pos

theorem exists_oriented_immersion_admissibility
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hb : b ∈ U) (n : Ambient) (hn : IsUnitNormalAt F n b)
    (hrank : (secondFundamental F n b).rank = 1) :
    ∃ R ∈ orientationRotations, ∃ V : Set Coord,
      IsOpen V ∧ (0 : Coord) ∈ V ∧ V ⊆ affineCoordinates b R ⁻¹' U ∧
      SmoothPositiveOn (affinePullbackMetric g b R) V ∧
      IsometricOn (affinePullbackMetric g b R) (affinePullbackImmersion F b R) V ∧
      ∀ p ∈ V,
        let gR := affinePullbackMetric g b R
        let zR := height (affinePullbackImmersion F b R) n
        (covHessian gR zR p).det = gaussianCurvature gR p * heightEnergy gR zR p ∧
        0 < heightEnergy gR zR p ∧ covHessian gR zR p 1 1 ≠ 0 ∧
        |covHessian gR zR p 0 1 / covHessian gR zR p 1 1| ≤ (1 / 100 : ℝ) := by
  have hz := height_smooth hF.1 n
  have hnpoint := geometric_height_normal_point hF hU hb hn
  have hsym : (covHessian g (height F n) b)ᵀ = covHessian g (height F n) b := by
    ext i j
    exact covHessian_symm hg hU hz hb j i
  have hHrank : (covHessian g (height F n) b).rank = 1 := by
    rw [hnpoint.2]
    exact hrank
  obtain ⟨R, hRnet, hRyy, hRq⟩ :=
    exists_orientationRotation_for_rank_one (covHessian g (height F n) b) hsym hHrank
  have hRinj := mulVec_injective_of_transpose_mul_eq_one R
    (orientationRotations_properties hRnet).1
  let W := affineCoordinates b R ⁻¹' U
  let gR := affinePullbackMetric g b R
  let FR := affinePullbackImmersion F b R
  let zR := height FR n
  have hWo : IsOpen W := isOpen_affine_preimage hU b R
  have h0W : (0 : Coord) ∈ W := by
    change affineCoordinates b R 0 ∈ U
    simpa only [affineCoordinates_zero] using hb
  have hgR : SmoothPositiveOn gR W := affinePullbackMetric_smoothPositive hg b R hRinj
  have hFR : IsometricOn gR FR W := affinePullbackImmersion_isometric hF hU b R
  have hzR : ContDiffOn ℝ ∞ zR W := height_smooth hFR.1 n
  have hcritR : fderiv ℝ zR 0 = 0 := by
    change fderiv ℝ ((height F n) ∘ affineCoordinates b R) 0 = 0
    apply fderiv_affine_comp_eq_zero b R 0
    · simpa only [affineCoordinates_zero] using
        (((hz b hb).contDiffAt (hU.mem_nhds hb)).differentiableAt (by simp))
    · simpa only [affineCoordinates_zero] using hnpoint.1
  have hHR : covHessian gR zR 0 = Rᵀ * covHessian g (height F n) b * R := by
    change covHessian (affinePullbackMetric g b R)
      ((height F n) ∘ affineCoordinates b R) 0 = _
    exact covHessian_affinePullback_at_zero g hz hU b R hb hnpoint.1
  have hyyR : covHessian gR zR 0 1 1 ≠ 0 := by rw [hHR]; exact hRyy
  have hqR : |covHessian gR zR 0 0 1 / covHessian gR zR 0 1 1| < (1 / 100 : ℝ) := by
    rw [hHR]
    exact hRq
  obtain ⟨V, hVo, h0V, hVW, hVad⟩ :=
    exists_open_admissibility_at_critical hgR hzR hWo h0W hcritR hyyR hqR
  refine ⟨R, hRnet, V, hVo, h0V, hVW, ?_, ?_, ?_⟩
  · exact ⟨fun i j => (hgR.1 i j).mono hVW, fun p hp => hgR.2 p (hVW hp)⟩
  · exact ⟨hFR.1.mono hVW, fun p hp => hFR.2 p (hVW hp)⟩
  · intro p hp
    have heq := geometric_height_equation hgR hFR hWo n hn.1 (hVW hp)
    have had := hVad p hp
    refine ⟨?_, had.1, had.2.1, had.2.2.le⟩
    simpa only [heightEnergy, mul_assoc] using heq

end SmoothLocal.Geometry

end

end OAI
