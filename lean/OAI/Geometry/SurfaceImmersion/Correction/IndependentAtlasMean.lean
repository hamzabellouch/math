import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanApproximation
import OAI.Geometry.SurfaceImmersion.Correction.CrossAtlasPolynomialTransfer
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorBounds
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasShiftedBounds

namespace OAI

/-! The slow mean solver uses its good atlas while the primitive keeps its own. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization WeightedEstimates
local instance independentMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance independentMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance independentMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem polynomial_mean_approximation_in_atlas (data : MetricGoodPhaseData g F)
    (B : SmoothingAtlas M) {n : B.centers → ℕ}
    (Pol : ∀ i : B.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (R N : ℕ) (σmax : ℝ) (hσmax : 0 < σmax) :
    ∃ (b u η L C : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ b < σmax ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ (∀ m, 0 ≤ P m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∃ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G ∧
      B.WeightedBound 1 3 (L*z^u) (G-F) ∧
      (∀ m, B.ShiftedBound 2 m (z^b) (P m) G) ∧
      B.TensorWeightedBound 1 R (C*z^N) (B.atlasPolynomialMetric Pol z G-g.inner) := by
  obtain ⟨Q,hQ,hrep⟩ := data.A.cross_atlas_polynomial_transfer B Pol hPol
  obtain ⟨b,u,η,L,C,P,hb,hb16,hbσ,hu,hη,hη1,hL,hC,hP,hfamily⟩ :=
    data.polynomial_mean_approximation Q hQ hF hmetric R N σmax hσmax
  obtain ⟨Dv,hDv,hv⟩ := data.A.weightedBound_change_atlas (V := Space) B 3
  obtain ⟨Dt,hDt,ht⟩ := data.A.tensorWeightedBound_change_atlas B R
  choose Ds hDs hs using fun m : ℕ => data.A.shiftedBound_change_atlas (V := Space) B 2 m
  refine ⟨b,u,η,Dv*L,Dt*C,(fun m => Ds m*P m),hb,hb16,hbσ,hu,hη,hη1,
    mul_nonneg hDv hL,mul_nonneg hDt hC,fun m => mul_nonneg (hDs m) (hP m),?_⟩
  intro z hz hzη
  obtain ⟨G,hG,hclose,hshift,herror⟩ := hfamily z hz hzη
  have hz1 := hzη.le.trans hη1
  have hbz : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hbz1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have herr : data.A.TensorWeightedBound 1 R (C*z^N)
      (B.atlasPolynomialMetric Pol z G-g.inner) := by
    rw [← hrep G hG z]
    exact herror
  refine ⟨G,hG,?_,?_,?_⟩
  · have hh := hv (G-F) 1 (L*z^u) zero_lt_one le_rfl
      (mul_nonneg hL (Real.rpow_nonneg hz.le _)) (hG.sub hF) hclose
    simpa only [mul_assoc] using hh
  · intro m
    exact hs m G (z^b) (P m) hbz hbz1 (hP m) hG (hshift m)
  · have hh := ht _ 1 (C*z^N) zero_lt_one le_rfl
      (mul_nonneg hC (pow_nonneg hz.le _))
      ((B.atlasPolynomialMetric_smooth hPol hG z).sub_section g.contMDiff) herr
    simpa only [mul_assoc] using hh

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
