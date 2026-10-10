import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Atlas.ChartReadSupport

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance overlapTargetsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance overlapTargetsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance overlapTargetsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

def globalQuadraticSupport {ι : Type*} (S : ι → Set M) : RealModes.QuadraticLabel ι → Set M
  | .inl a => S a
  | .inr ⟨a,b,_⟩ => S a ∩ S b

omit [ChartedSpace Plane M] [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma globalQuadraticSupport_closed {ι : Type*} (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) :
    ∀ l : RealModes.QuadraticLabel ι, IsClosed (globalQuadraticSupport S l) := by
  intro l
  rcases l with a | ⟨a,b,c⟩
  · exact hS a
  · exact (hS a).inter (hS b)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quadraticOverlapCompact (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) : TopologicalSpace.Compacts JetPolynomial.Base :=
  ⟨(chart (k : M)) '' (tsupport (A.weight k) ∩ globalQuadraticSupport S l),
    ((isClosed_tsupport _).inter (globalQuadraticSupport_closed S hS l)).isCompact.image_of_continuousOn
      ((chart (k : M)).continuousOn.mono (fun _ h => A.weight_support k h.1))⟩

omit [Fintype ι] [DecidableEq ι] in
lemma quadraticOverlapCompact_subset (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    (A.quadraticOverlapCompact S hS k l : Set JetPolynomial.Base) ⊆ A.chartWeightCompact k := by
  rintro x ⟨p,hp,rfl⟩
  exact ⟨p,hp.1,rfl⟩

omit [Fintype ι] [DecidableEq ι] in
lemma globalQuadraticTarget_overlap (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    tsupport (A.globalQuadraticTarget τ φ Z hφ hZ k l) ⊆
      (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) := by
  intro x hx
  let Q := RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
    (fun a => A.vectorPlaneRead k (Z a)) l
  have hw : x ∈ tsupport (fun y => (A.planeWeight k y)^2) :=
    tsupport_smul_subset_left (fun y => (A.planeWeight k y)^2) Q hx
  have hw' : x ∈ tsupport (A.planeWeight k) := by
    have hs : tsupport (fun y => (A.planeWeight k y)^2) ⊆ tsupport (A.planeWeight k) := by
      simpa only [pow_two] using (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    exact hs hw
  have hkx : x ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) :=
    (A.supportedPlaneWeight k).tsupport_subset hw'
  have hq : x ∈ tsupport Q := tsupport_smul_subset_right (fun y => (A.planeWeight k y)^2) Q hx
  have hqq := RealModes.quadraticAmplitude_tsupport τ (fun a => A.vectorPlaneRead k (φ a))
    (fun a => A.vectorPlaneRead k (Z a)) (fun _ => Subset.rfl) l hq
  have hpx : (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ globalQuadraticSupport S l := by
    rcases l with a | ⟨a,b,c⟩
    · exact hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq)
    · exact ⟨hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq.1),
        hSZ b (A.vectorPlaneRead_support_on_weight k (Z b) hkx hqq.2)⟩
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hkx
  have hpS : p ∈ globalQuadraticSupport S l := by
    simpa only [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv (A.weight_support k hp)] using hpx
  exact ⟨chart (k : M) p,⟨p,⟨hp,hpS⟩,rfl⟩,rfl⟩

def globalQuadraticTargetRestricted (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.quadraticOverlapCompact S hS k l)) :=
  ContDiffMapSupportedIn.of_support_subset (A.globalQuadraticTarget τ φ Z hφ hZ k l).contDiff
    (subset_closure.trans (A.globalQuadraticTarget_overlap τ φ Z hφ hZ S hS hSZ k l))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
