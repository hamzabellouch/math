import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFiberInverse
import OAI.Geometry.SurfaceImmersion.Geometry.TensorBundleInverse
import OAI.Geometry.SurfaceImmersion.Primitive.CurvedAtlasPrimitives

namespace OAI

/-! The actual fiberwise correction operator for independently perturbed
primitive cutoffs. Its reference value is the identity, and its inverse
solves the finite rank-one equation on the original tensor bundle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance atlasOperatorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasOperatorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasOperatorFiberComplete : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance atlasOperatorDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasOperatorDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasOperatorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasOperatorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance atlasOperatorSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (atlasOperatorSectionNormed p).toAddCommGroup

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def primitiveCoefficientField (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (a : A.centers × Fin 3) (p : M) : TensorFiber →L[ℝ] ℝ :=
  ((P a.1 (chart (a.1 : M) p)).Q a.2).comp
    (fiberToThree.comp (show TensorFiber →L[ℝ] TensorFiber from
      (A.tensorTriv a.1).continuousLinearMapAt ℝ p))

def primitivePhaseCovector (phi : (A.centers × Fin 3) → M → ℝ)
    (a : A.centers × Fin 3) (p : M) : Plane →L[ℝ] ℝ :=
  mfderiv planeModel 𝓘(ℝ) (phi a) p

def primitiveFullOperator (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (p : M) : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p :=
  completedPrimitiveOperator (fun a => A.primitiveCoefficientField P a p)
    (fun a => psi a p) (fun a => A.primitivePhaseCovector phi a p)

lemma local_primitive_operator_decomposition
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (P i (chart (i : M) p)).ξ j = phaseDerivative (phi i j) (coordinateChart (i : M) p))
    (i : A.centers) {p : M} (hp : p ∈ tsupport (A.weight i))
    (B : CovariantTwoTensor p) (hB : ∀ v w, B v w = B w v) :
    ∑ j : Fin 3, A.primitiveCoefficientField P (i,j) p B •
      (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
        (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p) = B := by
  let C : TensorFiber := (A.tensorTriv i).continuousLinearMapAt ℝ p B
  let T := (trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
  let u : ∀ x : M, CovariantTwoTensor x := fun _ => (show TensorFiber from B)
  have hpS := A.weight_support i hp
  have hC : ∀ v w, C v w = C w v := by
    intro v w
    change A.bundleComponent A.tensorTriv i u p v w = A.bundleComponent A.tensorTriv i u p w v
    rw [A.tensorComponent_apply i u hpS,A.tensorComponent_apply i u hpS]
    exact hB _ _
  have hd := congrArg fiberFromThree ((P i (chart (i : M) p)).decomposition (fiberToThree C))
  simp only [map_sum,map_smul] at hd
  rw [fiberFromThree_toThree C hC] at hd
  have hval (j : Fin 3) (v : Plane) :
      A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p v =
        phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T v)) := by
    rw [primitivePhaseCovector,A.curvedAtlasPhase_mfderiv phi hphi (i,j) (houter i) hp,
      A.coordinateChart_tangentCoordinates i hpS]
    change fderiv ℝ (phi i j) (coordinateChart (i : M) p) (planeCoordinates (T v)) = _
    rw [hfit i j p hp,phaseLinear_phaseDerivative]
  ext v w
  have he := congrArg (fun D : TensorFiber => D (T v) (T w)) hd
  simp only [sum_apply,smul_apply,smul_eq_mul,fiberFromThree_apply,covectorSquare_evaluate] at he
  have heB : C (T v) (T w) = B v w := A.tensorComponent_tangentCoordinates i u hpS v w
  simp only [sum_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,hval]
  change (∑ j : Fin 3, (P i (chart (i : M) p)).Q j (fiberToThree C) *
    (phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T v)) *
      phaseLinear ((P i (chart (i : M) p)).ξ j) (planeCoordinates (T w)))) = _
  exact he.trans heB

/-- At the original square partition the completed operator is exactly the
identity, on the full tensor fiber rather than only on a quotient. -/
theorem primitiveFullOperator_reference
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hfit : ∀ i j p, p ∈ tsupport (A.weight i) →
      (P i (chart (i : M) p)).ξ j = phaseDerivative (phi i j) (coordinateChart (i : M) p))
    (p : M) :
    A.primitiveFullOperator P (fun a => A.weight a.1) (A.curvedAtlasPhase phi) p =
      ContinuousLinearMap.id ℝ (CovariantTwoTensor p) := by
  apply completedPrimitiveOperator_eq_id
  intro B hB
  rw [finitePrimitiveOperator_apply,tensorSymmetrizer_eq_self hB,
    ← Finset.univ_product_univ,Finset.sum_product]
  have hi (i : A.centers) :
      (∑ j : Fin 3, ((A.weight i p)^2*A.primitiveCoefficientField P (i,j) p B) •
        (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
          (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) = (A.weight i p)^2 • B := by
    by_cases hw : A.weight i p = 0
    · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_smul,Finset.sum_const_zero]
    · rw [show (∑ j : Fin 3, ((A.weight i p)^2*A.primitiveCoefficientField P (i,j) p B) •
          (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
            (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) =
          (A.weight i p)^2 • (∑ j : Fin 3, A.primitiveCoefficientField P (i,j) p B •
            (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p).smulRight
              (A.primitivePhaseCovector (A.curvedAtlasPhase phi) (i,j) p)) by
            simp only [Finset.smul_sum,smul_smul]]
      rw [A.local_primitive_operator_decomposition P phi hphi houter hfit i
        (subset_tsupport _ hw) B hB]
  simp_rw [hi]
  rw [← Finset.sum_smul,A.partition p,one_smul]

/-- The corrected tensor is obtained by actual pointwise inverse. -/
def correctedPrimitiveTensor (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (p : M) : CovariantTwoTensor p :=
  (A.primitiveFullOperator P psi phi p).inverse (u p)

theorem correctedPrimitiveTensor_reconstruct
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p) (hsymm : ∀ p v w, u p v w = u p w v) (p : M) :
    (∀ v w, A.correctedPrimitiveTensor P psi phi u p v w =
      A.correctedPrimitiveTensor P psi phi u p w v) ∧
    (∑ a : A.centers × Fin 3, ((psi a p)^2 * A.primitiveCoefficientField P a p
      (A.correctedPrimitiveTensor P psi phi u p)) •
      (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) = u p := by
  obtain ⟨hs,he⟩ := completedPrimitiveOperator_inverse_symmetric
    (fun a => A.primitiveCoefficientField P a p) (fun a => psi a p)
    (fun a => A.primitivePhaseCovector phi a p) (hinv p) (hsymm p)
  refine ⟨hs,?_⟩
  rw [finitePrimitiveOperator_apply] at he
  simpa only [correctedPrimitiveTensor,primitiveFullOperator,tensorSymmetrizer_eq_self hs] using! he

/-- Smoothness is the ordinary smooth inverse theorem on the tensor bundle. -/
theorem correctedPrimitiveTensor_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hoperator : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.correctedPrimitiveTensor P psi phi u p)) :=
  tensorBundle_inverse_apply_smooth _ hoperator hinv u hu

def correctedPrimitiveAmplitude (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (a : A.centers × Fin 3) (p : M) : ℝ :=
  psi a p * Real.sqrt (A.primitiveCoefficientField P a p
    (A.correctedPrimitiveTensor P psi phi u p))

lemma correctedPrimitiveAmplitude_square
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 ≤ A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) (p : M) :
    (A.correctedPrimitiveAmplitude P psi phi u a p)^2 =
      (psi a p)^2*A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p) := by
  by_cases hp : psi a p = 0
  · simp only [correctedPrimitiveAmplitude,hp,zero_mul,zero_pow (by decide : 2 ≠ 0)]
  · rw [correctedPrimitiveAmplitude,mul_pow,Real.sq_sqrt (hpos a p (subset_tsupport _ hp))]

/-- Independent supports retain the exact global rank-one tensor identity. -/
theorem correctedPrimitiveAmplitude_reconstruct
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p) (hsymm : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 ≤ A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (p : M) :
    (∑ a : A.centers × Fin 3, (A.correctedPrimitiveAmplitude P psi phi u a p)^2 •
      (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) = u p := by
  simp_rw [A.correctedPrimitiveAmplitude_square P psi phi u hpos]
  exact (A.correctedPrimitiveTensor_reconstruct P psi phi hinv u hsymm p).2

lemma correctedPrimitiveAmplitude_pos_iff
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) (p : M) :
    0 < A.correctedPrimitiveAmplitude P psi phi u a p ↔ 0 < psi a p := by
  constructor
  · intro h
    exact (mul_pos_iff.mp h).resolve_right
      (fun hh => (Real.sqrt_nonneg _).not_gt hh.2) |>.1
  · intro h
    exact mul_pos h (Real.sqrt_pos.mpr (hpos a p (subset_tsupport _ h.ne')))

lemma correctedPrimitiveAmplitude_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (hoperator : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a) := by
  have hu' := A.correctedPrimitiveTensor_smooth P psi phi hoperator hinv u hu
  apply contMDiff_of_tsupport
  intro p hp
  have hps : p ∈ tsupport (psi a) := tsupport_mul_subset_left hp
  have hpchart := hsupport a hps
  have hc := ((chart_smooth (a.1 : M)) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hq := (hQ a p hps).contMDiffAt.comp p hc
  have hb := ((A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain a.1 hu') p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hf := (fiberToThree.contDiff (n := ∞)).contDiffAt.contMDiffAt.comp p hb
  have he := hq.clm_apply hf
  have hr := (Real.contDiffAt_sqrt (hpos a p hps).ne').contMDiffAt.comp p he
  exact (hpsi a p).mul hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
