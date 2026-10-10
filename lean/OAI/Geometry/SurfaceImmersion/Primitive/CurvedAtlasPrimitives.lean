import OAI.Geometry.SurfaceImmersion.Atlas.SpatialPhaseBasis
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedCoordinateChange
import OAI.Geometry.SurfaceImmersion.Primitive.PositiveAtlasPrimitives

namespace OAI

/-! Positive primitive amplitudes for point-dependent phase bases.
The basis can be the actual nonlinear gradient basis constructed in
`SpatialPhaseBasis`; no constant-phase restriction enters the algebra. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance curvedPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance curvedPrimitiveDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

def curvedPhaseCoefficient (i : A.centers) (j : Fin 3) (y : JetPolynomial.Base) : ℝ :=
  (P i y).Q j (fiberToThree (A.tensorEncode u y i))

def curvedPhaseTensor (i : A.centers) (j : Fin 3) : JetPolynomial.Base → TensorFiber :=
  fun y => A.curvedPhaseCoefficient P u i j y • fiberFromThree (covectorSquare ((P i y).ξ j))

def curvedPrimitiveAmplitude (a : A.centers × Fin 3) (p : M) : ℝ :=
  A.weight a.1 p * Real.sqrt
    ((P a.1 (chart (a.1 : M) p)).Q a.2 (A.tensorChartRead a.1 u (chart (a.1 : M) p)))

def curvedPrimitiveTensor (a : A.centers × Fin 3) (p : M) : CovariantTwoTensor p :=
  (A.curvedPrimitiveAmplitude P u a p)^2 •
    A.bundleRestore A.tensorTriv a.1
      (fun y => fiberFromThree (covectorSquare ((P a.1 y).ξ a.2))) p

lemma curvedPrimitiveAmplitude_support (a : A.centers × Fin 3) :
    tsupport (A.curvedPrimitiveAmplitude P u a) ⊆ tsupport (A.weight a.1) :=
  tsupport_mul_subset_left

lemma curvedPrimitiveAmplitude_nonneg
    (hw : ∀ i p, 0 ≤ A.weight i p) (a : A.centers × Fin 3) (p : M) :
    0 ≤ A.curvedPrimitiveAmplitude P u a p :=
  mul_nonneg (hw a.1 p) (Real.sqrt_nonneg _)

lemma curvedPrimitiveAmplitude_pos_iff
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i (chart (i : M) p)).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) (p : M) :
    0 < A.curvedPrimitiveAmplitude P u a p ↔ 0 < A.weight a.1 p := by
  constructor
  · intro h
    exact (mul_pos_iff.mp h).resolve_right (fun hh => (Real.sqrt_nonneg _).not_gt hh.2) |>.1
  · intro h
    exact mul_pos h (Real.sqrt_pos.mpr (hpos a.1 a.2 p (subset_tsupport _ h.ne')))

lemma curvedPrimitiveAmplitude_square (i : A.centers) (j : Fin 3)
    (hpos : ∀ p ∈ tsupport (A.weight i),
      0 ≤ (P i (chart (i : M) p)).Q j (A.tensorChartRead i u (chart (i : M) p)))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    (A.curvedPrimitiveAmplitude P u (i,j) p)^2 =
      A.curvedPhaseCoefficient P u i j (chart (i : M) p) := by
  unfold curvedPhaseCoefficient
  rw [A.tensorEncode_read i u hp,map_smul]
  by_cases hz : A.weight i p = 0
  · simp only [curvedPrimitiveAmplitude,hz,zero_mul,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · dsimp only [curvedPrimitiveAmplitude]
    rw [mul_pow,Real.sq_sqrt (hpos p (subset_tsupport _ hz))]
    rfl

lemma sum_curvedPhaseTensor (hu : ∀ p v w, u p v w = u p w v)
    (y : JetPolynomial.Base) (i : A.centers) :
    ∑ j : Fin 3, A.curvedPhaseTensor P u i j y = A.tensorEncode u y i := by
  change (∑ j : Fin 3, (P i y).Q j (fiberToThree (A.tensorEncode u y i)) •
    fiberFromThree (covectorSquare ((P i y).ξ j))) = _
  calc
    _ = fiberFromThree (∑ j : Fin 3,
        (P i y).Q j (fiberToThree (A.tensorEncode u y i)) • covectorSquare ((P i y).ξ j)) := by
      simp only [map_sum,map_smul]
    _ = _ := by
      rw [(P i y).decomposition,fiberFromThree_toThree _ (A.tensorEncode_symmetric hu y i)]

lemma restored_curvedPrimitiveTensor (i : A.centers) (j : Fin 3)
    (hpos : ∀ p ∈ tsupport (A.weight i),
      0 ≤ (P i (chart (i : M) p)).Q j (A.tensorChartRead i u (chart (i : M) p))) (p : M) :
    A.curvedPrimitiveTensor P u (i,j) p =
      A.bundleRestore A.tensorTriv i (A.curvedPhaseTensor P u i j) p := by
  by_cases hp : p ∈ (chart (i : M)).source
  · unfold curvedPrimitiveTensor
    rw [A.curvedPrimitiveAmplitude_square P u i j hpos hp]
    simp only [bundleRestore,curvedPhaseTensor,map_smul,smul_smul]
    rw [mul_comm]
  · have ho : A.outer i p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (A.outer_support i h))
    simp only [curvedPrimitiveTensor,bundleRestore,ho,zero_smul,smul_zero]

/-- The actual curved-basis amplitudes give an exact finite decomposition. -/
theorem sum_curvedPrimitiveTensor (hu : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i (chart (i : M) p)).Q j (A.tensorChartRead i u (chart (i : M) p))) (p : M) :
    ∑ a : A.centers × Fin 3, A.curvedPrimitiveTensor P u a p = u p := by
  rw [← Finset.univ_product_univ,Finset.sum_product]
  simp_rw [A.restored_curvedPrimitiveTensor P u _ _ (hpos _ _) p]
  have hi (i : A.centers) :
      (∑ j : Fin 3, A.bundleRestore A.tensorTriv i (A.curvedPhaseTensor P u i j) p) =
        A.bundleRestore A.tensorTriv i (fun y => A.tensorEncode u y i) p := by
    simp only [bundleRestore,← Finset.smul_sum,← map_sum]
    rw [A.sum_curvedPhaseTensor P u hu]
  simp_rw [hi]
  exact congrFun (A.tensorDecode_encode u) p

def curvedAtlasPhase (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (a : A.centers × Fin 3) : M → ℝ :=
  restore (a.1 : M) (A.outer a.1) (phi a.1 a.2 ∘ JetPolynomial.planeCoordinateIsometry)

lemma curvedAtlasPhase_smooth (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j)) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.curvedAtlasPhase phi a) :=
  restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
    ((hphi a.1 a.2).comp JetPolynomial.planeCoordinateIsometry.contDiff)

lemma curvedAtlasPhase_eventually (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (a : A.centers × Fin 3)
    (houter : ∀ p ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    A.curvedAtlasPhase phi a =ᶠ[𝓝 p] (phi a.1 a.2 ∘ coordinateChart (a.1 : M)) := by
  filter_upwards [houter p hp,
    (chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hp)] with x hx hxs
  rw [curvedAtlasPhase,restore,indicator_of_mem hxs,hx,one_smul]
  rfl

lemma curvedAtlasPhase_mfderiv (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j)) (a : A.centers × Fin 3)
    (houter : ∀ p ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p =
      (fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p)).comp
        (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (a.1 : M)) p) := by
  have he := A.curvedAtlasPhase_eventually phi a houter hp
  have hd := he.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  have hpS : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hp
  have hc := ((coordinateChart_smoothOn (a.1 : M)) p hpS).contMDiffAt
    ((coordinateChart (a.1 : M)).open_source.mem_nhds hpS)
  rw [mfderiv_comp p
    ((hphi a.1 a.2).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv] at hd
  change (mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p : Plane →L[ℝ] ℝ) =
    (ContinuousLinearMap.id ℝ ℝ).comp
      ((fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p)).comp
        (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (a.1 : M)) p)) at hd
  simpa only [ContinuousLinearMap.id_comp] using hd

/-- Every restored tensor is the actual square of its global phase
covector wherever its amplitude is supported. -/
lemma curvedPrimitiveTensor_apply
    (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (P i (chart (i : M) p)).ξ j = phaseDerivative (phi i j) (coordinateChart (i : M) p))
    (a : A.centers × Fin 3) (p : M) (v w : TangentSpace planeModel p) :
    A.curvedPrimitiveTensor P u a p v w =
      (A.curvedPrimitiveAmplitude P u a p)^2 *
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p v) *
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p w) := by
  by_cases ha : A.curvedPrimitiveAmplitude P u a p = 0
  · simp only [curvedPrimitiveTensor,ha,zero_pow (by decide : 2 ≠ 0),zero_smul,zero_apply]
    let dv : ℝ := mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p v
    let dw : ℝ := mfderiv planeModel 𝓘(ℝ) (A.curvedAtlasPhase phi a) p w
    change (0 : ℝ) = (0 : ℝ) * dv * dw
    exact ((congrArg (fun x : ℝ => x * dw) (zero_mul dv)).trans (zero_mul dw)).symm
  · have hp := A.curvedPrimitiveAmplitude_support P u a (subset_tsupport _ ha)
    have hpS := A.weight_support a.1 hp
    change (A.curvedPrimitiveAmplitude P u a p)^2 *
      A.bundleRestore A.tensorTriv a.1
        (fun y => fiberFromThree (covectorSquare ((P a.1 y).ξ a.2))) p v w = _
    rw [A.tensorRestore_apply a.1 _ hpS, A.outer_one a.1 p hp,one_mul,
      fiberFromThree_apply,covectorSquare_evaluate,hfit a.1 a.2 p hp,
      phaseLinear_phaseDerivative,
      A.curvedAtlasPhase_mfderiv phi hphi a (houter a.1) hp,
      A.coordinateChart_tangentCoordinates a.1 hpS]
    let dv : ℝ := (fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p))
      (planeCoordinates ((trivializationAt Plane (TangentSpace planeModel) (a.1 : M)).continuousLinearMapAt ℝ p v))
    let dw : ℝ := (fderiv ℝ (phi a.1 a.2) (coordinateChart (a.1 : M) p))
      (planeCoordinates ((trivializationAt Plane (TangentSpace planeModel) (a.1 : M)).continuousLinearMapAt ℝ p w))
    change (A.curvedPrimitiveAmplitude P u a p)^2 * (dv * dw) =
      (A.curvedPrimitiveAmplitude P u a p)^2 * dv * dw
    ring

variable [CompactSpace M]

lemma curvedPrimitiveAmplitude_smooth
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hQ : ∀ i j p, p ∈ tsupport (A.weight i) →
      ContDiffAt ℝ ∞ (fun y => (P i y).Q j) (chart (i : M) p))
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i (chart (i : M) p)).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.curvedPrimitiveAmplitude P u a) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hpw := A.curvedPrimitiveAmplitude_support P u a hp
  have hc := ((chart_smooth (a.1 : M)) p (A.weight_support a.1 hpw)).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hpw))
  have hr := (A.tensorChartRead_smooth a.1 hu).contMDiff.contMDiffAt.comp p hc
  have hq := (hQ a.1 a.2 p hpw).contMDiffAt.comp p hc
  have he := hq.clm_apply hr
  have hroot := (Real.contDiffAt_sqrt (hpos a.1 a.2 p hpw).ne').contMDiffAt.comp p he
  exact (A.weight_smooth a.1 p).mul hroot

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
