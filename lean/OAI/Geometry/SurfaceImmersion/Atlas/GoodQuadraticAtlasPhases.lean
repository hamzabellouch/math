import OAI.Geometry.SurfaceImmersion.Atlas.AtlasCompactPhaseWeights
import OAI.Geometry.SurfaceImmersion.Atlas.ActualPhaseGoodness
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedAtlasPhases

namespace OAI

/-! The actual restored global phases have good quadratic interactions. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- A single choice of positive frequencies makes every actual quadratic
phase good on the compact support where its amplitude can be nonzero. -/
theorem exists_good_quadratic_atlas_phases {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hpure : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)) :
    ∃ w : A.centers → Fin 3 → ℝ, (∀ i j, 0 < w i j) ∧
      ∀ k l x, x ∈ (modeSupport
        (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
          (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
          (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x) := by
  classical
  let φ := A.linearAtlasPhase Q (fun _ _ => 1)
  have hφ (a : A.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (φ a) :=
    A.linearAtlasPhase_smooth Q (fun _ _ => 1) a
  have hpoint (k : A.centers) (p : M) (hp : p ∈ tsupport (A.weight k)) :
      coordinateChart (k : M) p ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) :=
    ⟨chart (k : M) p,⟨p,hp,rfl⟩,rfl⟩
  obtain ⟨v,hv,hpairs⟩ := A.exists_overlap_phase_weights hF φ hφ
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1)) (fun _ => isClosed_tsupport _)
    (fun k p hp => hImm k _ (hpoint k p hp))
    (fun k a p hpk hpa => A.linearAtlasPhase_unit_read_good hF Q houter hImm hpure a k hpa hpk)
  let w : A.centers → Fin 3 → ℝ := fun i j => v (i,j)
  refine ⟨w,fun i j => hv (i,j),?_⟩
  intro k l x hx
  change x ∈ planeCoordinateIsometry '' ((chart (k : M)) ''
    (tsupport (A.weight k) ∩ globalQuadraticSupport
      (fun a : A.centers × Fin 3 => tsupport (A.weight a.1)) l)) at hx
  rcases hx with ⟨y,⟨p,⟨hpk,hpl⟩,rfl⟩,rfl⟩
  have he : coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l) =
      quadraticPhase (fun a => A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) l := by
    funext z
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  change Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
    (coordinateChart (k : M) p))
    (phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) l)
      (coordinateChart (k : M) p))
  have hd (a : A.centers × Fin 3) :=
    (A.vectorPlaneRead_smooth k (A.linearAtlasPhase_smooth Q w a)).differentiable (by simp)
      (coordinateChart (k : M) p)
  have hscale (a : A.centers × Fin 3) :
      phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) (coordinateChart (k : M) p) =
        v a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) := by
    exact A.linearAtlasPhase_read_derivative_smul_unit Q w a k _
  rcases l with a | ⟨a,b,c⟩
  · change Good _ (phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) _)
    rw [phaseDerivative_const_smul (hd a) 2,hscale]
    exact good_smul (by norm_num : (2 : ℝ) ≠ 0)
      (good_smul (hv a).ne' (A.linearAtlasPhase_unit_read_good hF Q houter hImm hpure a k hpl hpk))
  · have hpairs' := hpairs k a b.1 b.2.symm p hpk hpl.1 hpl.2
    cases c
    · change Good _ (phaseDerivative
        (A.vectorPlaneRead k (A.linearAtlasPhase Q w a) +
         A.vectorPlaneRead k (A.linearAtlasPhase Q w b.1)) _)
      rw [phaseDerivative_add (hd a) (hd b.1),hscale,hscale]
      exact hpairs'.1
    · change Good _ (phaseDerivative
        (A.vectorPlaneRead k (A.linearAtlasPhase Q w a) -
         A.vectorPlaneRead k (A.linearAtlasPhase Q w b.1)) _)
      rw [phaseDerivative_sub (hd a) (hd b.1),hscale,hscale]
      exact hpairs'.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
