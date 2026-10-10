import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticOverlapSupports
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCombinedModes

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance polynomialOverlapFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialOverlapFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialOverlapDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialOverlapDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialOverlapSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialOverlapSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)


namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma globalPolynomialQuadraticTarget_overlap {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    tsupport (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) ⊆
      (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) := by
  intro x hx
  let V := combinedQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
    (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l
  have hw : x ∈ tsupport (fun y => (A.planeWeight k y)^2) :=
    tsupport_smul_subset_left (fun y => (A.planeWeight k y)^2) V hx
  have hw' : x ∈ tsupport (A.planeWeight k) := by
    have hs : tsupport (fun y => (A.planeWeight k y)^2) ⊆ tsupport (A.planeWeight k) := by
      simpa only [pow_two] using
        (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    exact hs hw
  have hkx := (A.supportedPlaneWeight k).tsupport_subset hw'
  have hv : x ∈ tsupport V := tsupport_smul_subset_right (fun y => (A.planeWeight k y)^2) V hx
  have hqq : x ∈ RealModes.quadraticSupport (fun a => tsupport (A.vectorPlaneRead k (Z a))) l := by
    have hadd := tsupport_add
      (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
        (fun a => A.vectorPlaneRead k (Z a)) l)
      (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) hv
    rcases hadd with hm | hp
    · exact RealModes.quadraticAmplitude_tsupport τ _ _ (fun _ => Subset.rfl) l hm
    · have hc := tsupport_comp_preimage
        (quadraticFamilyTensor (Q k) ε (A.jetChartMap k F)
          (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l)
        planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous hp
      have hh := quadraticFamilyTensor_tsupport (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0
        (fun a => isClosed_tsupport (A.vectorChartRead k (Z a))) (fun _ => Subset.rfl) l hc
      have hread (a) (ha : planeCoordinateIsometry.symm x ∈ tsupport (A.vectorChartRead k (Z a))) :
          x ∈ tsupport (A.vectorPlaneRead k (Z a)) := by
        have he : A.vectorPlaneRead k (Z a) ∘ planeCoordinateIsometry = A.vectorChartRead k (Z a) := by
          funext y
          simp only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
        rw [← he] at ha
        have hv := tsupport_comp_preimage (A.vectorPlaneRead k (Z a)) planeCoordinateIsometry
          planeCoordinateIsometry.continuous ha
        simpa only [Set.mem_preimage,planeCoordinateIsometry.apply_symm_apply] using hv
      rcases l with a | ⟨a,b,c⟩
      · exact hread a hh
      · exact ⟨hread a hh.1,hread b hh.2⟩
  have hpx : (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ globalQuadraticSupport S l := by
    rcases l with a | ⟨a,b,c⟩
    · exact hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq)
    · exact ⟨hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq.1),
        hSZ b (A.vectorPlaneRead_support_on_weight k (Z b) hkx hqq.2)⟩
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hkx
  have hpS : p ∈ globalQuadraticSupport S l := by
    simpa only [planeCoordinateIsometry.symm_apply_apply,
      (chart (k : M)).left_inv (A.weight_support k hp)] using hpx
  exact ⟨chart (k : M) p,⟨p,⟨hp,hpS⟩,rfl⟩,rfl⟩

def globalPolynomialQuadraticTargetRestricted {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.quadraticOverlapCompact S hS k l)) :=
  ContDiffMapSupportedIn.of_support_subset
    (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l).contDiff
    (subset_closure.trans
      (A.globalPolynomialQuadraticTarget_overlap Q hQ F hF ε τ φ Z hφ hZ S hS hSZ k l))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
