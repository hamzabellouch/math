import OAI.Geometry.SurfaceImmersion.Correction.AtlasSupportedPolynomialVariation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanSupport
import OAI.Geometry.SurfaceImmersion.Correction.AtlasRestoredPolynomialDirection

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance quadraticSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance quadraticSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance quadraticSupportDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance quadraticSupportDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance quadraticSupportSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance quadraticSupportSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)


/-- A quadratic variation vanishes wherever its varying field vanishes as a germ. -/
lemma second_variation_zero_of_notMem (e : Expression) (G : Base → JetPolynomial.Space)
    {H : Base → JetPolynomial.Space} {p : Base} (hp : p ∉ tsupport H) (t : ℝ) :
    (e.variations 1).eval ![G,H,H,0] (p,t) = 0 := by
  let J : DirectionJets := fun w a p => (jet H w a p : ℂ)
  have hz : quadraticComplex e G J J (p,t) = 0 := by
    apply quadraticComplex_zero_at
    intro w a
    change (jet H w a p : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H w a h))]
    rfl
  have he := quadraticComplex_real_fields e G H H (p,t)
  rw [show quadraticComplex e G (fun w a p => (jet H w a p : ℂ))
    (fun w a p => (jet H w a p : ℂ)) (p,t) = 0 from hz] at he
  exact Complex.ofReal_eq_zero.mp he.symm

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma atlasPolynomialQuadratic_zero_of_notMem {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X : M → Space) {p : M} (hp : p ∉ tsupport X) :
    A.atlasPolynomialQuadratic P ε F X p = 0 := by
  classical
  unfold atlasPolynomialQuadratic tensorPlaneRestore
  apply Finset.sum_eq_zero
  intro i _
  by_cases ho : A.outer i p = 0
  · simp only [bundleRestore,ho,zero_smul]
  · have hps := A.outer_support i (subset_tsupport (A.outer i) ho)
    have hz := A.jetChartMap_eventually_zero i hps (notMem_tsupport_iff_eventuallyEq.mp hp)
    have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
      notMem_tsupport_iff_eventuallyEq.mpr hz
    have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
        planeCoordinateIsometry = A.jetChartMap i X := by
      funext y
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    have he : coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
        (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
      funext k
      simp only [coordinateQuadraticPolynomial,hcomp,
        planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [second_variation_zero_of_notMem (P i k l) (A.jetChartMap i F) hn 0,mul_zero,mul_zero]
    simp only [bundleRestore,he,map_zero,smul_zero]


theorem supported_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F X : M → Space)
    (hsp : tsupport X ⊆ tsupport (A.weight i)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x) :
    A.atlasPolynomialQuadratic P ε F X = A.bundleRestore A.tensorTriv i
      (fun x => fiberFromThree (coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x))) := by
  funext p
  by_cases hp : p ∈ tsupport (A.weight i)
  · have he := A.restore_chart_read_on_weight i (A.atlasPolynomialQuadratic P ε F X) hp
      (A.tensorPlaneRestore_symmetric _ p)
    have hr := hread (chart (i : M) p) ⟨p,hp,rfl⟩
    change _ = A.outer i p • (A.tensorTriv i).symmL ℝ p (fiberFromThree _)
    rw [hr]
    exact he.symm
  · have hX : p ∉ tsupport X := fun hx => hp (hsp hx)
    rw [A.atlasPolynomialQuadratic_zero_of_notMem P ε F X hX]
    by_cases ho : A.outer i p = 0
    · simp only [bundleRestore,ho,zero_smul]
    · have hsource := A.outer_support i (subset_tsupport (A.outer i) ho)
      have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
        notMem_tsupport_iff_eventuallyEq.mpr
          (A.jetChartMap_eventually_zero i hsource (notMem_tsupport_iff_eventuallyEq.mp hX))
      have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
          planeCoordinateIsometry = A.jetChartMap i X := by
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
      have hz : coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
          (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        funext k
        simp only [coordinateQuadraticPolynomial,hcomp,
          planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
        apply Finset.sum_eq_zero
        intro l _
        rw [second_variation_zero_of_notMem (Q k l) (A.jetChartMap i F) hn 0,mul_zero,mul_zero]
      simp only [bundleRestore,hz,map_zero,smul_zero]


theorem restored_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F : M → Space) (X : RealModes.RField 4)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateQuadraticPolynomial Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F
          (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry))) x) :
    A.atlasPolynomialQuadratic P ε F
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateQuadraticPolynomial Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x))) := by
  have hs := A.restore_plane_tsupport i (spaceCoordinates.symm ∘ X)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hsp)
  have he : A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  have hh := A.supported_polynomial_quadratic P i Q F
    (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) hs ε
  simpa only [he] using hh (by simpa only [he] using hread)


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
