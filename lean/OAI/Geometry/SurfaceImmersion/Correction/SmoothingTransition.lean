import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothingLinearity
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedCompositionBounds

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def transition (p q : M) : OpenPartialHomeomorph Base Base := (chart p).symm.trans (chart q)

lemma transition_smooth (p q : M) :
    ContDiffOn ℝ ∞ (transition p q) (transition p q).source := by
  apply ContMDiffOn.contDiffOn
  exact (chart_smooth q).comp
    ((chart_symm_smooth p).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def pairWeight (i j : A.centers) : Base → ℝ := localize (i : M) (A.weight i) (A.outer j)

def pairSupport (i j : A.centers) : Set Base :=
  (chart (i : M)) '' (tsupport (A.weight i) ∩ tsupport (A.outer j))

variable [CompactSpace M]

lemma pairWeight_smooth (i j : A.centers) : ContDiff ℝ ∞ (A.pairWeight i j) :=
  localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (A.outer_smooth j)

lemma pairWeight_support (i j : A.centers) : tsupport (A.pairWeight i j) ⊆ A.pairSupport i j :=
  localize_tsupport_inter (i : M) (A.weight_support i) (A.outer j)

lemma pairSupport_compact (i j : A.centers) : IsCompact (A.pairSupport i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (A.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma pairSupport_transition (i j : A.centers) :
    A.pairSupport i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p, ⟨hp, hq⟩, rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp', ?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact A.outer_support j hq

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → WeightedBound Set.univ s m C h →
      WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
