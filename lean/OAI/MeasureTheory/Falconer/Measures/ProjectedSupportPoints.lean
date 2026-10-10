import OAI.MeasureTheory.Falconer.Measures.ChooseProjectedFrostman

namespace OAI

/-! # Original support points separated by a nonatomic projected law -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem distinct_projected_support_points (μ : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space m)
    [NullSingletonClass ((μ : Measure (Space d)).map P)] :
    ∃ x ∈ (μ : Measure (Space d)).support,
      ∃ y ∈ (μ : Measure (Space d)).support, P x ≠ P y := by
  obtain ⟨x,hx⟩ := (μ : Measure (Space d)).nonempty_support (by
    intro h
    have hh := congrArg (fun η : Measure (Space d) => η univ) h
    simp at hh)
  let F : Set (Space d) := P ⁻¹' {P x}
  have hFm : MeasurableSet F := (measurableSet_singleton _).preimage P.continuous.measurable
  have hF : (μ : Measure (Space d)) F = 0 := by
    rw [show F = P ⁻¹' {P x} from rfl,
      ← Measure.map_apply P.continuous.measurable (measurableSet_singleton _)]
    exact measure_singleton _
  have hFc : (μ : Measure (Space d)) Fᶜ = 1 := by
    rw [measure_compl hFm (measure_ne_top _ _),hF,measure_univ,tsub_zero]
  obtain ⟨y,hy,hyS⟩ := (μ : Measure (Space d)).nonempty_inter_support_of_pos
    (s := Fᶜ) (by rw [hFc]; exact zero_lt_one)
  refine ⟨x,hx,y,hyS,?_⟩
  intro he
  exact hy (by simpa only [F,mem_preimage,mem_singleton_iff] using he.symm)

theorem positive_compact_support_ball (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    {x : Space d} (hx : x ∈ (μ : Measure (Space d)).support) {r : ℝ} (hr : 0 < r) :
    IsCompact ((μ : Measure (Space d)).support ∩ closedBall x r) ∧
      0 < (μ : Measure (Space d)) ((μ : Measure (Space d)).support ∩ closedBall x r) := by
  refine ⟨hK.inter_right isClosed_closedBall,?_⟩
  have hp := ((μ : Measure (Space d)).mem_support_iff_forall x).mp hx
    (ball x r) (ball_mem_nhds x hr)
  have hsub : ball x r ⊆ ((μ : Measure (Space d)).support ∩ closedBall x r) ∪
      (μ : Measure (Space d)).supportᶜ := by
    intro y hy
    by_cases hs : y ∈ (μ : Measure (Space d)).support
    · exact Or.inl ⟨hs,ball_subset_closedBall hy⟩
    · exact Or.inr hs
  have hh := (measure_mono (μ := (μ : Measure (Space d))) hsub).trans
    (measure_union_le _ _)
  rw [Measure.measure_compl_support,add_zero] at hh
  exact hp.trans_le hh

end Falconer

end OAI
