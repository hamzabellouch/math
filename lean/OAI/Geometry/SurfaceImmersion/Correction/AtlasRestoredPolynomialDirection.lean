import OAI.Geometry.SurfaceImmersion.Correction.AtlasSupportedPolynomialVariation
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasDifferential

namespace OAI

/-! A supported Euclidean field is restored with exactly its original
localized jet, so the local polynomial solver acts on the actual direction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance restoredDirectionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredDirectionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredDirectionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredDirectionDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredDirectionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredDirectionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma jetChartMap_restored_direction (i : A.centers) (X : RealModes.RField 4)
    (hX : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) = X ∘ planeCoordinateIsometry := by
  have hsp := (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hX
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · change spaceCoordinates (localize (i : M) (A.outer i)
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) x) = _
    rw [localize,indicator_of_mem hx,A.restore_plane_in_coordinates i _ hsp hx]
    simp only [Function.comp_apply,map_smul,ContinuousLinearEquiv.apply_symm_apply]
    by_cases hz : X (planeCoordinateIsometry x) = 0
    · rw [hz,smul_zero]
    · have hp : (chart (i : M)).symm x ∈ tsupport (A.weight i) := by
        apply A.mem_weight_support_of_plane i ((chart (i : M)).map_target hx)
        rw [(chart (i : M)).right_inv hx]
        exact hX (subset_tsupport X hz)
      rw [A.outer_one i _ hp,one_pow,one_smul]
  · have hz : X (planeCoordinateIsometry x) = 0 := by
      by_contra hn
      obtain ⟨y,hy,he⟩ := hX (subset_tsupport X hn)
      have hyx : y = x := planeCoordinateIsometry.injective he
      subst y
      obtain ⟨p,hp,rfl⟩ := hy
      exact hx ((chart (i : M)).map_source (A.weight_support i hp))
    change spaceCoordinates (localize (i : M) (A.outer i) _ x) = _
    rw [localize,indicator_of_notMem hx,map_zero]
    exact hz.symm

theorem restored_polynomial_direction {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F : M → Space) (X : RealModes.RField 4)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateRealLinearized Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialVariation P ε F
          (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry))) x) :
    A.atlasPolynomialVariation P ε F
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateRealLinearized Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x))) := by
  have hs := A.restore_plane_tsupport i (spaceCoordinates.symm ∘ X)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hsp)
  have he : A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  have hh := A.supported_polynomial_variation P i Q F
    (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) hs ε
  simpa only [he] using hh (by simpa only [he] using hread)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
