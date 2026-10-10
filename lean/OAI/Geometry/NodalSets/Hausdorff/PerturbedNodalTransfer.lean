import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SpherePositiveMargins
import OAI.Geometry.NodalSets.Charts.TargetShortCircleArc
import OAI.Geometry.NodalSets.Elliptic.IntrinsicPairUniformBounds
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundPerturbation
import OAI.Geometry.NodalSets.Hausdorff.HausdorffDistortion
import OAI.Geometry.NodalSets.Hausdorff.IntrinsicUniformNodal

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance perturbedNodalTransferLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance perturbedNodalTransferLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance perturbedNodalTransferLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance perturbedNodalTransferLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance perturbedNodalTransferLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance perturbedNodalTransferLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance perturbedNodalTransferLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

lemma small_round_correction_bounds (A : IntrinsicTensor) (rho alpha beta : Base → ℝ)
    {c B R : ℝ}
    (hlo : ∀ x v, c*roundCotangentTensor x v v ≤ A x v v)
    (hhi : ∀ x v, A x v v ≤ B*roundCotangentTensor x v v)
    (hrlo : ∀ x, c ≤ rho x) (hrhi : ∀ x, rho x ≤ R)
    (ha : ∀ x, |alpha x| ≤ min (c/2) 1) (hb : ∀ x, |beta x| ≤ min (c/2) 1) :
    (∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫ = 0 →
      (c/2)*‖v‖^2 ≤ (A x+roundTensorPerturbation alpha x)
        (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) ∧
    (∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫ = 0 →
      (A x+roundTensorPerturbation alpha x)
        (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ (B+1)*‖v‖^2) ∧
    (∀ x, c/2 ≤ rho x+beta x) ∧ (∀ x, rho x+beta x ≤ R+1) := by
  have hab (x : Base) := abs_le.mp (ha x)
  have hbb (x : Base) := abs_le.mp (hb x)
  refine ⟨?_,?_,?_,?_⟩
  · intro x v hv
    have hh := hlo x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at hh
    change _ ≤ A x _ _ + roundTensorPerturbation alpha x _ _
    rw [roundTensorPerturbation_tangent alpha x v v hv hv,real_inner_self_eq_norm_sq]
    have hal : -(c/2) ≤ alpha x := (neg_le_neg (min_le_left _ _)).trans (hab x).1
    nlinarith [mul_le_mul_of_nonneg_right hal (sq_nonneg ‖v‖)]
  · intro x v hv
    have hh := hhi x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at hh
    change A x _ _ + roundTensorPerturbation alpha x _ _ ≤ _
    rw [roundTensorPerturbation_tangent alpha x v v hv hv,real_inner_self_eq_norm_sq]
    have hal : alpha x ≤ 1 := (hab x).2.trans (min_le_right _ _)
    nlinarith [mul_le_mul_of_nonneg_right hal (sq_nonneg ‖v‖)]
  · intro x
    have hh := (neg_le_neg (min_le_left (c/2) 1)).trans (hbb x).1
    linarith [hrlo x]
  · intro x
    have hh := (hbb x).2.trans (min_le_right (c/2) 1)
    linarith [hrhi x]

lemma circleLift_productChartInverse (f : Base → ℝ) (a b : ℝ) (q : Circle) (z : Coord × ℝ) :
    circleLift f (productChartInverse (seedPoint,q) a b z) = f (seedSphereFromCoord z.1) := by
  unfold circleLift productChartInverse
  rw [extChartAt_prod]
  rfl

theorem uniform_small_correction_nodal_transfer (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    {H : Set Coord} (hH : IsCompact H) :
    ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (alpha beta : Base → ℝ)
        (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation alpha x))
        (hnewSym : ∀ x v w, (A x+roundTensorPerturbation alpha x) v w =
          (A x+roundTensorPerturbation alpha x) w v)
        (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v)
        (hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+beta x))
        (hrnewPos : ∀ x, 0 < rho x+beta x),
        (∀ x, |alpha x| ≤ eta) → (∀ x, |beta x| ≤ eta) →
        ∀ (u : Coord → ℝ) (ug : Base → ℝ) (U : Set Coord), U ⊆ H →
          (∀ x, ug (seedSphereFromCoord x) = u x) →
          Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : Coord × ℝ | u z.1 = 0}) ≤
            (C:ℝ≥0∞)^4 * nodalMeasure
              (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation alpha x) hnew hnewSym hnewPos
                (fun x ↦ rho x+beta x) hrnew hrnewPos) (circleLift ug) := by
  obtain ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,hrhi⟩ := intrinsic_pair_uniform_bounds A hA hs hp rho hr hrp
  obtain ⟨a,b,hb,hchart⟩ := exists_short_circle_arc (seedPoint,(1:Circle))
  obtain ⟨C,hC,htransfer⟩ := uniform_intrinsic_coefficient_nodal_transfer
    (c/2) (B+1) (c/2) (R+1) (by positivity) (by positivity) (by positivity) (by positivity)
    (seedPoint,(1:Circle)) a hb.ne' (hH.prod isCompact_Icc)
    (hchart (fun y hy ↦ by rw [centeredSphereChart_target]; trivial))
  refine ⟨min (c/2) 1,by positivity,C,hC,?_⟩
  intro alpha beta hnew hnewSym hnewPos hrnew hrnewPos ha hb u ug U hUH he
  obtain ⟨hblo,hbhi,hbrlo,hbrhi⟩ := small_round_correction_bounds A rho alpha beta hlo hhi hrlo hrhi ha hb
  apply htransfer _ hnew hnewSym hnewPos _ hrnew hrnewPos hblo hbhi hbrlo hbrhi
  · rintro z ⟨hz,hzero⟩
    exact ⟨hUH hz.1,hz.2⟩
  · rintro z ⟨hz,hzero⟩
    rw [circleLift_productChartInverse,he]
    exact hzero

end
end Yau.Target

end OAI
