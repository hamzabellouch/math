import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation
import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartRead

namespace OAI

/-! The actual change of tensor coordinates for a restored atlas term.
Bundle restoration uses one outer cutoff, whereas chart reading uses the
square of its own cutoff. On the nonzero partition locus the latter is one. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

local instance transitionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance transitionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance transitionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance transitionDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance transitionSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance transitionSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorChartRead_bundleRestore_transition (i j : A.centers) (f : Base → TensorFiber)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv j f) x =
      A.outer j ((chart (i : M)).symm x) •
        fiberToThree (A.bundleTransition A.tensorTriv i j x
          (f (transition (i : M) (j : M) x))) := by
  have hi : x ∈ (chart (i : M)).target := hx.1
  have hread := congrFun
    (A.bundleCutoff_restore A.tensorTriv A.tensorTriv_domain i j (A.outer i) f) x
  have hcut : localize (i : M) (A.outer i) (A.outer j) x =
      A.outer j ((chart (i : M)).symm x) := by
    simp only [localize,indicator_of_mem hi,ho,one_pow,one_smul]
  change fiberToThree (A.bundleCutoff A.tensorTriv i (A.outer i)
    (A.bundleRestore A.tensorTriv j f) x) = _
  rw [hread,hcut,map_smul]

lemma tensorChartRead_bundleRestore_of_weight_ne_zero (i j : A.centers)
    (f : Base → TensorFiber) {x : Base}
    (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv j f) x =
      A.outer j ((chart (i : M)).symm x) •
        fiberToThree (A.bundleTransition A.tensorTriv i j x
          (f (transition (i : M) (j : M) x))) :=
  A.tensorChartRead_bundleRestore_transition i j f hx
    (A.outer_one i _ (subset_tsupport (A.weight i) hw))

lemma tensorChartRead_bundleRestore_eventually (i j : A.centers)
    (f : Base → TensorFiber) {x : Base}
    (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv j f) =ᶠ[𝓝 x]
      (fun y => A.outer j ((chart (i : M)).symm y) •
        fiberToThree (A.bundleTransition A.tensorTriv i j y
          (f (transition (i : M) (j : M) y)))) := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((chart (i : M)).continuousAt_symm hx.1)
  filter_upwards [(transition (i : M) (j : M)).open_source.mem_nhds hx,ho]
    with y hy hoy
  exact A.tensorChartRead_bundleRestore_transition i j f hy hoy

/-- The three-coordinate form of the genuine tensor-bundle transition,
including the single cutoff used by restoration. -/
def tensorRestoreTransition (i j : A.centers) (x : Base) : Tensor →L[ℝ] Tensor :=
  A.outer j ((chart (i : M)).symm x) •
    fiberToThree.comp ((A.bundleTransition A.tensorTriv i j x).comp fiberFromThree)

lemma tensorRestoreTransition_smoothOn (i j : A.centers) :
    ContDiffOn ℝ ∞ (A.tensorRestoreTransition i j)
      (transition (i : M) (j : M)).source := by
  have hB := A.bundleTransition_smooth A.tensorTriv A.tensorTriv_domain i j
  have hleft : ContDiffOn ℝ ∞ (fun _ : Base => fiberToThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  have hright : ContDiffOn ℝ ∞ (fun _ : Base => fiberFromThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  have ha : ContDiffOn ℝ ∞ (fun x : Base => A.outer j ((chart (i : M)).symm x))
      (chart (i : M)).target :=
    ((A.outer_smooth j).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  exact (ha.mono (fun _ hx => hx.1)).smul (hleft.clm_comp (hB.clm_comp hright))

lemma tensorChartRead_restoreThree (i j : A.centers) (f : Base → Tensor)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i
        (A.bundleRestore A.tensorTriv j (fun y => fiberFromThree (f y))) x =
      A.tensorRestoreTransition i j x (f (transition (i : M) (j : M) x)) := by
  rw [A.tensorChartRead_bundleRestore_transition i j _ hx ho]
  rfl

lemma weighted_tensorChartRead_restoreThree (i j : A.centers) (f : Base → Tensor)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source) :
    (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        A.tensorChartRead i
          (A.bundleRestore A.tensorTriv j (fun y => fiberFromThree (f y))) x =
      (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        A.tensorRestoreTransition i j x (f (transition (i : M) (j : M) x)) := by
  by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · rw [A.tensorChartRead_restoreThree i j f hx
      (A.outer_one i _ (subset_tsupport (A.weight i) hw))]

/-- The finite-dimensional tensor transition extends smoothly off any
compact overlap. The extension is independent of the restored field. -/
theorem compact_tensorRestoreTransition (i j : A.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ L : Base → Tensor →L[ℝ] Tensor, ContDiff ℝ ∞ L ∧
        EqOn L (A.tensorRestoreTransition i j) U ∧
        (∀ (f : Base → Tensor) (x : Base), x ∈ U →
          (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              A.tensorChartRead i
                (A.bundleRestore A.tensorTriv j (fun y => fiberFromThree (f y))) x =
            (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              L x (f (transition (i : M) (j : M) x))) := by
  obtain ⟨U,hU,hKU,hUe,L,hL,he⟩ := CollarVelocity.compact_smooth_extension hK
    (transition (i : M) (j : M)).open_source hKe
    (A.tensorRestoreTransition_smoothOn i j)
  refine ⟨U,hU,hKU,hUe,L,hL,he,?_⟩
  intro f x hx
  rw [he hx]
  exact A.weighted_tensorChartRead_restoreThree i j f (hUe hx)

variable [CompactSpace M]

theorem pair_tensorRestoreTransition (i j : A.centers) :
    ∃ U : Set Base, IsOpen U ∧ A.pairSupport i j ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ L : Base → Tensor →L[ℝ] Tensor, ContDiff ℝ ∞ L ∧
        EqOn L (A.tensorRestoreTransition i j) U ∧
        (∀ (f : Base → Tensor) (x : Base), x ∈ U →
          (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              A.tensorChartRead i
                (A.bundleRestore A.tensorTriv j (fun y => fiberFromThree (f y))) x =
            (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              L x (f (transition (i : M) (j : M) x))) :=
  A.compact_tensorRestoreTransition i j (A.pairSupport_compact i j)
    (A.pairSupport_transition i j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
