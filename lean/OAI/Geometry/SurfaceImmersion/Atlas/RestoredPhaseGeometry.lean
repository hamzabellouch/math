import OAI.Geometry.SurfaceImmersion.Atlas.GlobalPhaseGerms
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticOverlapSupports
import OAI.Geometry.Immersion.ClosedSurface.LengthMargins

namespace OAI

/-! The actual restored phases inherit quantitative margins on their
original support intersections. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restoredLinearPhase_read_phaseDerivative (i k : A.centers) (ξ : SmallModes.Base)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hpi : p ∈ tsupport (A.weight i)) (hpk : p ∈ tsupport (A.weight k)) :
    phaseDerivative (A.vectorPlaneRead k
      (restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry)))
      (coordinateChart (k : M) p) = atlasPhaseCovector (i : M) (k : M) ξ p := by
  have hi : restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry) =ᶠ[𝓝 p]
      atlasPhase (i : M) ξ := by
    filter_upwards [houter i p hpi,
      (chart (i : M)).open_source.mem_nhds (A.weight_support i hpi)] with x ho hx
    rw [restore,indicator_of_mem hx,ho,one_smul]
    rfl
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hc := (coordinateChart (k : M)).continuousAt_symm
    ((coordinateChart (k : M)).map_source hpK)
  have ht : Tendsto (coordinateChart (k : M)).symm
      (𝓝 (coordinateChart (k : M) p)) (𝓝 p) := by
    simpa only [ContinuousAt,(coordinateChart (k : M)).left_inv hpK] using hc
  have he := (A.vectorPlaneRead_eventually_comp_coordinateInverse
    (restore (i : M) (A.outer i) (phaseLinear ξ ∘ planeCoordinateIsometry)) k
      (houter k) hpk).trans (hi.comp_tendsto ht)
  unfold phaseDerivative atlasPhaseCovector
  rw [he.fderiv_eq (𝕜 := ℝ)]
  rfl

variable [CompactSpace M]

theorem restored_quadratic_margin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι → A.centers) (ξ : ι → SmallModes.Base) (S : ι → Set M)
    (hS : ∀ a, IsClosed (S a)) (hSi : ∀ a, S a ⊆ tsupport (A.weight (i a)))
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (F : M → Space) {ε : ℝ}
    (hpure : ∀ a k p, p ∈ S a → p ∈ tsupport (A.weight k) →
      ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)‖ ≤
        ‖secondQuadratic
          (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
          (-(atlasPhaseCovector (i a : M) (k : M) (ξ a) p).2,
            (atlasPhaseCovector (i a : M) (k : M) (ξ a) p).1)‖)
    (hpairs : ∀ a b k p, a ≠ b → p ∈ S a → p ∈ S b → p ∈ tsupport (A.weight k) →
      let B := realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)
      let u := atlasPhaseCovector (i a : M) (k : M) (ξ a) p
      let v := atlasPhaseCovector (i b : M) (k : M) (ξ b) p
      ε*‖B‖ ≤ ‖secondQuadratic B (-(u+v).2,(u+v).1)‖ ∧
      ε*‖B‖ ≤ ‖secondQuadratic B (-(u-v).2,(u-v).1)‖) :
    let φ := fun a => restore (i a : M) (A.outer (i a)) (phaseLinear (ξ a) ∘ planeCoordinateIsometry)
    ∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) →
      ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖ ≤
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (-(phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).2,
            (phaseDerivative (coordinatePhase (A.globalQuadraticPhase φ k l)) y).1)‖ := by
  intro φ k l y hy
  change y ∈ planeCoordinateIsometry '' ((chart (k : M)) ''
    (tsupport (A.weight k) ∩ globalQuadraticSupport S l)) at hy
  rcases hy with ⟨_,⟨p,⟨hpk,hpl⟩,rfl⟩,rfl⟩
  have he : coordinatePhase (A.globalQuadraticPhase φ k l) =
      quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l := by
    funext x
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  change ε*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
    (coordinateChart (k : M) p)‖ ≤
    ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
      (coordinateChart (k : M) p))
      (-(phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l)
          (coordinateChart (k : M) p)).2,
        (phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (φ a)) l)
          (coordinateChart (k : M) p)).1)‖
  have hd (a : ι) : DifferentiableAt ℝ (A.vectorPlaneRead k (φ a))
      (coordinateChart (k : M) p) := by
    have hs := A.vectorPlaneRead_smooth k (restore_smooth (i a : M) (A.outer_smooth (i a))
      (A.outer_support (i a)) ((phaseLinear (ξ a)).contDiff.comp planeCoordinateIsometry.contDiff))
    exact hs.differentiable (by simp) _
  have hder (a : ι) (ha : p ∈ S a) :
      phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) =
        atlasPhaseCovector (i a : M) (k : M) (ξ a) p :=
    A.restoredLinearPhase_read_phaseDerivative (i a) k (ξ a) houter (hSi a ha) hpk
  rcases l with a | ⟨a,b,c⟩
  · change ε*‖_‖ ≤ ‖secondQuadratic _
      (-(phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (φ a)) _).2,
        (phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (φ a)) _).1)‖
    rw [phaseDerivative_const_smul (hd a) 2,hder a hpl,norm_secondQuadratic_rotated_smul]
    have hh := hpure a k p hpl hpk
    nlinarith [norm_nonneg (secondQuadratic
      (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
      (-(atlasPhaseCovector (i a : M) (k : M) (ξ a) p).2,
        (atlasPhaseCovector (i a : M) (k : M) (ξ a) p).1))]
  · have hh := hpairs a b.1 k p b.2.symm hpl.1 hpl.2 hpk
    cases c
    · change ε*‖_‖ ≤ ‖secondQuadratic _
        (-(phaseDerivative (A.vectorPlaneRead k (φ a)+A.vectorPlaneRead k (φ b.1)) _).2,
          (phaseDerivative (A.vectorPlaneRead k (φ a)+A.vectorPlaneRead k (φ b.1)) _).1)‖
      rw [phaseDerivative_add (hd a) (hd b.1),hder a hpl.1,hder b.1 hpl.2]
      exact hh.1
    · change ε*‖_‖ ≤ ‖secondQuadratic _
        (-(phaseDerivative (A.vectorPlaneRead k (φ a)-A.vectorPlaneRead k (φ b.1)) _).2,
          (phaseDerivative (A.vectorPlaneRead k (φ a)-A.vectorPlaneRead k (φ b.1)) _).1)‖
      rw [phaseDerivative_sub (hd a) (hd b.1),hder a hpl.1,hder b.1 hpl.2]
      exact hh.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
