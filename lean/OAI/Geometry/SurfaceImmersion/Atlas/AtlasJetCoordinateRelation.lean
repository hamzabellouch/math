import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTransition
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! The actual localized atlas maps on a coordinate overlap.  The transition
scalar is the square of the outer cutoff.  A nonzero partition weight gives
the needed equality of germs without any extra plateau hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def transitionScalar (i j : A.centers) (x : Base) : ℝ :=
  (A.outer j ((chart (i : M)).symm x)) ^ 2

lemma transitionScalar_smoothOn (i j : A.centers) :
    ContDiffOn ℝ ∞ (A.transitionScalar i j) (chart (i : M)).target := by
  exact ((A.outer_smooth j).comp_contMDiffOn
    (chart_symm_smooth (i : M))).contDiffOn.pow 2

lemma outer_eventually_one_of_weight_ne_zero (i : A.centers) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  have hn : ∀ᶠ q in 𝓝 p, A.weight i q ≠ 0 :=
    (isOpen_ne.preimage (A.weight_smooth i).continuous).mem_nhds hp
  filter_upwards [hn] with q hq
  exact A.outer_one i q (subset_tsupport (A.weight i) hq)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma vectorChartRead_transition (i j : A.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.vectorChartRead j G (transition (i : M) (j : M) x) =
      A.transitionScalar i j x • A.vectorChartRead i G x := by
  have hi : x ∈ (chart (i : M)).target := hx.1
  have hj : transition (i : M) (j : M) x ∈ (chart (j : M)).target :=
    (chart (j : M)).map_source hx.2
  have he : (chart (j : M)).symm (transition (i : M) (j : M) x) =
      (chart (i : M)).symm x :=
    (chart (j : M)).left_inv hx.2
  simp only [vectorChartRead, localize, indicator_of_mem hi, indicator_of_mem hj,
    he, ho, one_pow, one_smul, transitionScalar]

lemma vectorChartRead_transition_eventually (i j : A.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => A.vectorChartRead j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.transitionScalar i j y • A.vectorChartRead i G y) := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((chart (i : M)).continuousAt_symm hx.1)
  filter_upwards [(transition (i : M) (j : M)).open_source.mem_nhds hx,ho]
    with y hy hoy
  exact A.vectorChartRead_transition i j G hy hoy

lemma jetChartMap_transition (i j : A.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.jetChartMap j G (transition (i : M) (j : M) x) =
      A.transitionScalar i j x • A.jetChartMap i G x := by
  change spaceCoordinates (A.vectorChartRead j G (transition (i : M) (j : M) x)) = _
  rw [A.vectorChartRead_transition i j G hx ho]
  exact map_smul spaceCoordinates _ _

lemma jetChartMap_transition_eventually (i j : A.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => A.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.transitionScalar i j y • A.jetChartMap i G y) := by
  filter_upwards [A.vectorChartRead_transition_eventually i j G hx hw] with y hy
  change spaceCoordinates (A.vectorChartRead j G (transition (i : M) (j : M) y)) = _
  rw [hy]
  exact map_smul spaceCoordinates _ _

/-- The partition weight removes the boundary case where a germ equal to
one is unavailable. This identity holds on the whole transition domain. -/
lemma weighted_jetChartMap_transition (i j : A.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source) :
    (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        A.jetChartMap j G (transition (i : M) (j : M) x) =
      (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        (A.transitionScalar i j x • A.jetChartMap i G x) := by
  by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · rw [A.jetChartMap_transition i j G hx
      (A.outer_one i _ (subset_tsupport (A.weight i) hw))]

/-- A fixed compact overlap has a globally smooth transition scalar. It
is chosen before the map, and retains both the weighted identity everywhere
and the unweighted identity of germs on the nonzero weight locus. -/
theorem compact_jetChartMap_transition (i j : A.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ a : Base → ℝ, ContDiff ℝ ∞ a ∧ EqOn a (A.transitionScalar i j) U ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              A.jetChartMap j G (transition (i : M) (j : M) x) =
            (A.weight i ((chart (i : M)).symm x)) ^ 2 • (a x • A.jetChartMap i G x)) ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          A.weight i ((chart (i : M)).symm x) ≠ 0 →
            (fun y => A.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
              (fun y => a y • A.jetChartMap i G y)) := by
  obtain ⟨U,hU,hKU,hUe,a,ha,he⟩ := CollarVelocity.compact_smooth_extension hK
    (transition (i : M) (j : M)).open_source hKe
    ((A.transitionScalar_smoothOn i j).mono (fun _ hx => hx.1))
  refine ⟨U,hU,hKU,hUe,a,ha,he,?_,?_⟩
  · intro G x hx
    rw [he hx]
    exact A.weighted_jetChartMap_transition i j G (hUe hx)
  · intro G x hx hw
    filter_upwards [A.jetChartMap_transition_eventually i j G (hUe hx) hw,
      hU.mem_nhds hx] with y hy hyU
    rw [he hyU]
    exact hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
