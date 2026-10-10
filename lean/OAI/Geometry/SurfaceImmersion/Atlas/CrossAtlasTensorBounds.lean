import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasTensorTransition
import OAI.Geometry.SurfaceImmersion.Atlas.BundleAtlasBounds

namespace OAI

/-! Weighted tensor bounds persist when the finite correction atlas changes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossTensorBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossTensorBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossTensorBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossTensorBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance crossTensorBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTensorBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

lemma cross_tensor_localize_restore_bound (i : B.centers) (j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h →
      WeightedEstimates.WeightedBound univ s m C h →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h)) := by
  let L : Base → TensorFiber →L[ℝ] TensorFiber := fun x =>
    (A.tensorTriv j).coordChangeL ℝ (B.tensorTriv i) ((chart (i : M)).symm x)
  have hL : ContDiffOn ℝ ∞ L (transition (i : M) (j : M)).source := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_coordChangeL (A.tensorTriv j) (B.tensorTriv i)).comp
      ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
    intro x hx
    have hj : (chart (i : M)).symm x ∈ (chart (j : M)).source := hx.2
    exact ⟨A.tensorTriv_domain j hj,B.tensorTriv_domain i ((chart (i : M)).map_target hx.1)⟩
  have heq (h : Base → TensorFiber) :
      B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h) =
        fun x => localize (i : M) (B.weight i) (A.outer j) x •
          L x (h (transition (i : M) (j : M) x)) := by
    funext x
    by_cases hi : x ∈ (chart (i : M)).target
    · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
      · have hbi := B.tensorTriv_domain i ((chart (i : M)).map_target hi)
        have hbj := A.tensorTriv_domain j hj
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,map_smul]
        rw [(B.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ hbi,
          (A.tensorTriv j).symmL_apply (R := ℝ) hbj,
          ← (A.tensorTriv j).coordChangeL_apply (R := ℝ) (B.tensorTriv i) ⟨hbj,hbi⟩,smul_smul]
        rfl
      · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hj (A.outer_support j hh))
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,hz,zero_smul,map_zero,smul_zero]
    · simp only [bundleLocalize,localize,indicator_of_notMem hi,zero_smul]
  obtain ⟨D,hD,hd⟩ := compact_localized_clm_composition_bound
    (transition (i : M) (j : M)).open_source (B.cross_pairSupport_compact A i j)
    (B.cross_pairSupport_transition A i j)
    (localize_smooth (i : M) (B.weight_smooth i) (B.weight_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (B.weight_support i) (A.outer j))
    hL (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro h s C hs hs1 hC hh hb
  rw [heq]
  exact hd h s C hs hs1 hC hh hb

theorem tensorWeightedBound_change_atlas (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ p : M, CovariantTwoTensor p) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound s m C u → B.TensorWeightedBound s m (D*C) u := by
  classical
  choose D hD hd using fun (i : B.centers) (j : A.centers) =>
    A.cross_tensor_localize_restore_bound B i j m
  refine ⟨∑ i : B.centers,∑ j : A.centers,D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)),?_⟩
  intro u s C hs hs1 hC hu hb i
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j*C)
    (fun j => B.bundleLocalize B.tensorTriv i
      (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)))
    (fun j _ => (B.bundleLocalize_smooth B.tensorTriv B.tensorTriv_domain i
      (A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain j
        (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu))).contDiffOn)
    (fun j _ => hd i j _ s C hs hs1 hC
      (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu) (hb j))
  have he : B.bundleLocalize B.tensorTriv i u = fun x => ∑ j : A.centers,
      B.bundleLocalize B.tensorTriv i
        (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)) x := by
    have hu' : u = (fun p => ∑ j : A.centers,
        A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u) p) :=
      (funext (A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain u)).symm
    conv_lhs => rw [hu']
    exact B.bundleLocalize_sum B.tensorTriv Finset.univ i _
  change WeightedEstimates.WeightedBound univ s m _ (B.bundleLocalize B.tensorTriv i u)
  rw [he]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
