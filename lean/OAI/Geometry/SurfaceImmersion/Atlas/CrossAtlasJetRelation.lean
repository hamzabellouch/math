import OAI.Geometry.SurfaceImmersion.Atlas.AtlasJetCoordinateRelation

namespace OAI

/-! Localized jets can be transported between independently chosen atlases. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

def cross_transitionScalar (i : A.centers) (j : B.centers) (x : Base) : ℝ :=
  (B.outer j ((chart (i : M)).symm x)) ^ 2

lemma cross_transitionScalar_smoothOn (i : A.centers) (j : B.centers) :
    ContDiffOn ℝ ∞ (A.cross_transitionScalar B i j) (chart (i : M)).target := by
  exact ((B.outer_smooth j).comp_contMDiffOn
    (chart_symm_smooth (i : M))).contDiffOn.pow 2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma cross_vectorChartRead_transition (i : A.centers) (j : B.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    B.vectorChartRead j G (transition (i : M) (j : M) x) =
      A.cross_transitionScalar B i j x • A.vectorChartRead i G x := by
  have hi : x ∈ (chart (i : M)).target := hx.1
  have hj : transition (i : M) (j : M) x ∈ (chart (j : M)).target :=
    (chart (j : M)).map_source hx.2
  have he : (chart (j : M)).symm (transition (i : M) (j : M) x) =
      (chart (i : M)).symm x :=
    (chart (j : M)).left_inv hx.2
  simp only [vectorChartRead, localize, indicator_of_mem hi, indicator_of_mem hj,
    he, ho, one_pow, one_smul, cross_transitionScalar]

lemma cross_vectorChartRead_transition_eventually (i : A.centers) (j : B.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => B.vectorChartRead j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.cross_transitionScalar B i j y • A.vectorChartRead i G y) := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((chart (i : M)).continuousAt_symm hx.1)
  filter_upwards [(transition (i : M) (j : M)).open_source.mem_nhds hx,ho]
    with y hy hoy
  exact A.cross_vectorChartRead_transition B i j G hy hoy

lemma cross_jetChartMap_transition (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    B.jetChartMap j G (transition (i : M) (j : M) x) =
      A.cross_transitionScalar B i j x • A.jetChartMap i G x := by
  change spaceCoordinates (B.vectorChartRead j G (transition (i : M) (j : M) x)) = _
  rw [A.cross_vectorChartRead_transition B i j G hx ho]
  exact map_smul spaceCoordinates _ _

lemma cross_jetChartMap_transition_eventually (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => B.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.cross_transitionScalar B i j y • A.jetChartMap i G y) := by
  filter_upwards [A.cross_vectorChartRead_transition_eventually B i j G hx hw] with y hy
  change spaceCoordinates (B.vectorChartRead j G (transition (i : M) (j : M) y)) = _
  rw [hy]
  exact map_smul spaceCoordinates _ _

/-- The partition weight removes the boundary case where a germ equal to
one is unavailable. This identity holds on the whole transition domain. -/
lemma cross_weighted_jetChartMap_transition (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source) :
    (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        B.jetChartMap j G (transition (i : M) (j : M) x) =
      (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        (A.cross_transitionScalar B i j x • A.jetChartMap i G x) := by
  by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · rw [A.cross_jetChartMap_transition B i j G hx
      (A.outer_one i _ (subset_tsupport (A.weight i) hw))]

/-- A fixed compact overlap has a globally smooth transition scalar. It
is chosen before the map, and retains both the weighted identity everywhere
and the unweighted identity of germs on the nonzero weight locus. -/
theorem cross_compact_jetChartMap_transition (i : A.centers) (j : B.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ a : Base → ℝ, ContDiff ℝ ∞ a ∧ EqOn a (A.cross_transitionScalar B i j) U ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              B.jetChartMap j G (transition (i : M) (j : M) x) =
            (A.weight i ((chart (i : M)).symm x)) ^ 2 • (a x • A.jetChartMap i G x)) ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          A.weight i ((chart (i : M)).symm x) ≠ 0 →
            (fun y => B.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
              (fun y => a y • A.jetChartMap i G y)) := by
  obtain ⟨U,hU,hKU,hUe,a,ha,he⟩ := CollarVelocity.compact_smooth_extension hK
    (transition (i : M) (j : M)).open_source hKe
    ((A.cross_transitionScalar_smoothOn B i j).mono (fun _ hx => hx.1))
  refine ⟨U,hU,hKU,hUe,a,ha,he,?_,?_⟩
  · intro G x hx
    rw [he hx]
    exact A.cross_weighted_jetChartMap_transition B i j G (hUe hx)
  · intro G x hx hw
    filter_upwards [A.cross_jetChartMap_transition_eventually B i j G (hUe hx) hw,
      hU.mem_nhds hx] with y hy hyU
    rw [he hyU]
    exact hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
