import Mathlib
import OAI.Analysis.AffineBernstein.NormedInteriorLimits

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

section FiniteAreaCover
/- Subadditivity for a finite (not disjoint) measurable cover, including
 the nonintegrable convention for the left-hand Bochner integral. -/
lemma integral_le_sum_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {K : Set X} {S : ι → Set X} {f : X → ℝ}
    (hK : MeasurableSet K) (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ K) (hcover : K ⊆ ⋃ i, S i)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    (∫ x in K, f x ∂μ) ≤ ∑ i, ∫ x in S i, f x ∂μ := by
  classical
  by_cases hi : IntegrableOn f K μ
  · have his (i : ι) : Integrable ((S i).indicator f) μ :=
      (hi.mono_set (hsub i)).integrable_indicator (hS i)
    have hb : ∀ x, K.indicator f x ≤ ∑ i, (S i).indicator f x := by
      intro x
      have hp (i : ι) : 0 ≤ (S i).indicator f x := by
        by_cases hx : x ∈ S i
        · simpa only [Set.indicator_of_mem hx] using hn x (hsub i hx)
        · simp [hx]
      by_cases hx : x ∈ K
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
        rw [Set.indicator_of_mem hx]
        calc
          f x = (S i).indicator f x := (Set.indicator_of_mem hxi f).symm
          _ ≤ ∑ i, (S i).indicator f x := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ i)
      · simpa only [Set.indicator_of_notMem hx] using Finset.sum_nonneg (fun i _ => hp i)
    have hh := integral_mono (hi.integrable_indicator hK)
      (integrable_finsetSum _ fun i _ => his i) hb
    simpa only [integral_indicator hK,integral_finsetSum _ (fun i _ => his i),
      integral_indicator (hS _)] using hh
  · rw [integral_undef hi]
    exact Finset.sum_nonneg fun i _ => setIntegral_nonneg (hS i) (fun x hx => hn x (hsub i hx))
end FiniteAreaCover
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Compact inner containment in the actual interiors of the approximants. -/
theorem LocalDistanceConverges.eventually_normed_compact_interior
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) (hS : IsCompact S)
    (hSC : S ⊆ interior C) : ∀ᶠ j in atTop, S ⊆ interior (Cj j) := by
  classical
  have hex : ∀ x : S, ∃ r > 0, Metric.closedBall (x : E) r ⊆ C := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (x : E) (hSC x.2)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (by linarith)).trans
      (hball.trans interior_subset)⟩
  choose r hr hball using hex
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun x hx => Metric.ball x (r ⟨x, hx⟩ / 4))
    (fun x hx => Metric.ball_mem_nhds x (div_pos (hr ⟨x,hx⟩) (by norm_num)))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, Metric.ball (x : E) (r x / 4) ⊆ Cj j :=
    fun x _ => h.eventually_normed_ball_subset hclj hcvj hnej (hr x) (hball x)
  filter_upwards [(t.eventually_all).mpr he] with j hj
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact (isOpen_ball.subset_interior_iff.mpr (hj y hyt)) hxy

end AffineBernstein

end

end OAI
