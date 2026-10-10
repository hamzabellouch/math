import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactWordCost
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactGeneratingBalls
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric

namespace OAI

/-! # A proper chain metric from a compact generating neighborhood -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)
  (hbounded : ∀ x y : G, dist x y ≤ 1)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K)

local notation "N" => compactWeightedNorm K hK hbounded hsymm

include hbounded in
theorem metric_le_weightedDistance (x y : G) : dist x y ≤ N (x⁻¹ * y) := by
  have h := seminorm_le_weightedWordNorm (compactWordCost K hK)
    (metricGroupNorm (G := G)).toGroupSeminorm (metric_le_compactWordCost K hK hbounded)
    (x⁻¹ * y)
  change dist 1 (x⁻¹ * y) ≤ N (x⁻¹ * y) at h
  simpa only [dist_one_groupDifference] using h

include hball in
theorem weightedDistance_le_near {x y : G} (hxy : dist x y ≤ δ) :
    N (x⁻¹ * y) ≤ dist x y := by
  have hmem : x⁻¹ * y ∈ K := hball _ (by simpa only [dist_one_groupDifference] using hxy)
  have h := weightedWordNorm_le (compactWordCost K hK) (x⁻¹ * y)
  rw [compactWordCost_mem K hK _ hmem] at h
  have hreal : N (x⁻¹ * y) ≤ dist 1 (x⁻¹ * y) := by exact_mod_cast h
  simpa only [dist_one_groupDifference] using hreal

include hδ hball in
theorem weightedDistance_topology (s : Set G) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, N (x⁻¹ * y) < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hsub⟩ := hs x hx
    refine ⟨ε, hε, fun y hy => hsub ?_⟩
    simpa only [mem_ball, dist_comm] using (metric_le_weightedDistance K hK hsymm hbounded x y).trans_lt hy
  · intro hs x hx
    obtain ⟨ε, hε, hsub⟩ := hs x hx
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro y hy
    have hxy : dist x y < min δ ε := by simpa only [mem_ball, dist_comm] using hy
    exact hsub y ((weightedDistance_le_near K hK hsymm hbounded δ hball
      (lt_of_lt_of_le hxy (min_le_left _ _)).le).trans_lt
        (lt_of_lt_of_le hxy (min_le_right _ _)))

@[instance_reducible]
def weightedGroupMetric : MetricSpace G :=
  MetricSpace.ofDistTopology (fun x y => N (x⁻¹ * y))
    (by intro x; simp)
    (by intro x y; simpa only [mul_inv_rev, inv_inv] using (map_inv_eq_map (N) (x⁻¹ * y)).symm)
    (by
      intro x y z
      simpa only [mul_assoc, mul_inv_cancel_left] using map_mul_le_add (N) (x⁻¹ * y) (y⁻¹ * z))
    (weightedDistance_topology K hK hsymm hbounded δ hδ hball)
    (by intro x y h; exact inv_mul_eq_one.mp ((N).eq_one_of_map_eq_zero' _ h))

theorem weightedGroupMetric_isometric :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    IsIsometricSMul G G := by
  let m₀ : MetricSpace G := inferInstance
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  refine ⟨fun g => Isometry.of_dist_eq ?_⟩
  intro x y
  change @compactWeightedNorm G _ m₀ _ K hK hbounded hsymm ((g * x)⁻¹ * (g * y)) =
    @compactWeightedNorm G _ m₀ _ K hK hbounded hsymm (x⁻¹ * y)
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

include hδ hδ1 hball in
theorem weighted_ball_subset_compact_power (x : G) (R : ℝ) :
    {y | N (x⁻¹ * y) ≤ R} ⊆
      (fun g : G => x * g) '' (K ^ ⌈(4 / δ) * R + (4 / δ) + 1⌉₊) := by
  intro y hy
  have hb := wordLength_le_weightedNorm_add K hK hbounded hsymm hδ hδ1 hball (x⁻¹ * y)
  have hlen : compactWordLength K hK (x⁻¹ * y) ≤ ⌈(4 / δ) * R + (4 / δ) + 1⌉₊ := by
    have hreal := (hb.trans (by gcongr; exact hy)).trans (Nat.le_ceil ((4 / δ) * R + (4 / δ) + 1))
    exact_mod_cast hreal
  have hone : (1 : G) ∈ K := hball 1 (by simpa using hδ.le)
  exact ⟨x⁻¹ * y, wordLength_ball_subset_pow K hK hsymm hone _ hlen, by simp⟩

include hδ1 in
theorem weightedGroupMetric_proper [IsTopologicalGroup G] (hcompact : IsCompact K) :
    letI := weightedGroupMetric K hK hsymm hbounded δ hδ hball
    ProperSpace G := by
  let n₀ : GroupNorm G := N
  have hcontain (x : G) (R : ℝ) :=
    weighted_ball_subset_compact_power K hK hsymm hbounded δ hδ hδ1 hball x R
  have hcompactPow (n : ℕ) := isCompact_set_pow K hcompact n
  let := weightedGroupMetric K hK hsymm hbounded δ hδ hball
  constructor
  intro x R
  apply IsCompact.of_isClosed_subset
    ((hcompactPow ⌈(4 / δ) * R + (4 / δ) + 1⌉₊).image
      (continuous_const.mul continuous_id)) isClosed_closedBall
  intro y hy
  apply hcontain x R
  change n₀ (y⁻¹ * x) ≤ R at hy
  have he : n₀ (x⁻¹ * y) = n₀ (y⁻¹ * x) := by
    simpa only [mul_inv_rev, inv_inv] using map_inv_eq_map n₀ (y⁻¹ * x)
  exact he.trans_le hy

end PolycyclicRecognition

end

end OAI
