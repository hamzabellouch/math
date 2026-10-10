import Mathlib
import OAI.Probability.UnimodularPercolation.Criticality.ClusterCount

namespace OAI

/-! Strict operator-threshold gaps and infinite-cluster phase classification. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem strict_gap_of_critical_bounded [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hp1 : pc G < 1) (hb : OperatorBounded G (pc G)) : pc G < ptwo G := by
  obtain ⟨D, hDpos, hD⟩ := exists_degree_bound G hqt
  obtain ⟨A, hA⟩ := hb
  let c : ℝ := (4 * D) * ‖A‖
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let ε : ℝ := (1 - (pc G : ℝ)) / (2 * (c + 1))
  have hε : 0 < ε := div_pos (sub_pos.mpr hp1) (by positivity)
  have heq : ε * (2 * (c + 1)) = 1 - (pc G : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < 2 * (c + 1)))
  have hr1 : (pc G : ℝ) + ε < 1 := by nlinarith
  let r : unitInterval := ⟨(pc G : ℝ) + ε, add_nonneg (pc G).2.1 hε.le, hr1.le⟩
  have hpr : pc G < r := by change (pc G : ℝ) < (pc G : ℝ) + ε; linarith
  have hrb : OperatorBounded G r := by
    apply operatorBounded_of_quantitative_gap G hloc D hD (pc G) r
      (pc_pos G hloc hqt) hpr hr1 A hA
    change (((pc G : ℝ) + ε) - (pc G : ℝ)) * (4 * D) * ‖A‖ < 1 - ((pc G : ℝ) + ε)
    have he : (((pc G : ℝ) + ε) - (pc G : ℝ)) * (4 * D) * ‖A‖ = ε * c := by
      dsimp [c]
      ring
    rw [he]
    nlinarith
  exact hpr.trans_le (le_sSup hrb)

theorem unique_probability_zero_of_lt_pu [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pu G) :
    law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 0 := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  refine (law_invariant_zero_one G hconn hloc hqt p _
    (measurableSet_unique_infinite_cluster G) ?_).resolve_right ?_
  · intro a b hab
    ext ω
    exact unique_infinite_cluster_aut_iff G hab ω
  · intro he
    exact (not_le_of_gt hp) (sInf_le he)

theorem finite_count_empty_ae_of_lt_pu [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp0 : 0 < p) (hp : p < pu G) :
    ∀ᵐ ω ∂law p, (infiniteClusters G ω).Finite → infiniteClusters G ω = ∅ := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hp1 : p < 1 := hp.trans_le (pu G).2.2
  have ha (x : V) (R : Finset V) :
      ∀ᵐ ω ∂law p, ¬((cluster G ω x).Infinite ∧ InfiniteCover G R ω) := by
    have hz : law p {ω | (cluster G ω x).Infinite ∧ InfiniteCover G R ω} = 0 := by
      by_contra h
      have ht := unique_pos_of_cover_pos G hconn p hp0 hp1 x R (pos_iff_ne_zero.mpr h)
      rw [unique_probability_zero_of_lt_pu G hconn hloc hqt p hp] at ht
      exact lt_irrefl _ ht
    apply ae_iff.mpr
    simpa only [not_not] using hz
  have hall : ∀ᵐ ω ∂law p, ∀ x : V, ∀ R : Finset V,
      ¬((cluster G ω x).Infinite ∧ InfiniteCover G R ω) :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr (ha x)
  filter_upwards [hall] with ω hω
  intro hfin
  by_contra hn
  obtain ⟨C, hC⟩ := Set.nonempty_iff_ne_empty.mpr hn
  obtain ⟨hx, x, rfl⟩ := hC
  let f : Set V → V := fun C => if hc : C ∈ infiniteClusters G ω then
    Classical.choose hc.2 else x
  have hf (C : Set V) (hC : C ∈ infiniteClusters G ω) : C = cluster G ω (f C) := by
    simp only [f, dite_eq_left hC]
    exact Classical.choose_spec hC.2
  let R : Finset V := hfin.toFinset.image f
  apply hω x R ⟨hx, ?_⟩
  intro y hy
  have hc : cluster G ω y ∈ infiniteClusters G ω := ⟨hy, y, rfl⟩
  refine ⟨f (cluster G ω y), Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hc, rfl⟩, ?_⟩
  have he := hf _ hc
  exact (Set.ext_iff.mp he _).mpr (mem_cluster_self G ω (f (cluster G ω y)))

theorem infinitely_many_of_pc_lt_lt_pu [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hc : pc G < p) (hu : p < pu G) :
    ∀ᵐ ω ∂law p, (infiniteClusters G ω).Infinite := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have he : ∀ᵐ ω ∂law p, (infiniteClusters G ω).Nonempty := by
    rw [← map_openEdges p]
    apply (ae_map_iff (measurable_openEdges p).aemeasurable ?_).mpr
    · simpa only [infiniteClusters_nonempty_iff] using ae_exists_infinite_cluster_of_pc_lt G p hc
    · simpa only [infiniteClusters_nonempty_iff] using measurableSet_exists_infinite_cluster G
  filter_upwards [he, finite_count_empty_ae_of_lt_pu G hconn hloc hqt p
    ((pc_pos G hloc hqt).trans hc) hu] with ω hne hf
  intro hfin
  exact hne.ne_empty (hf hfin)
end Percolation

end OAI
