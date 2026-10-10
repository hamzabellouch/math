import OAI.Geometry.RCD.Metric.RescalingNetFamily

namespace OAI

/-! # Properness of the completed sampled limit

The uniform finite nets pass to the distance-matrix limit. Density then
extends their covers to its metric completion, proving properness.
-/

open Set Metric Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates.RescalingNetFamily

variable {X : Type*} [MetricSpace X] {p : X} {r : ℕ → ℝ}
  (s : RescalingNetFamily p r) (phi : ℕ → ℕ) (hr : ∀ i, 0 < r i)
  [PseudoMetricSpace s.Index]
  (hconv : ∀ a b, Tendsto
    (fun i => dist (s.sample (phi i) a) (s.sample (phi i) b) / r (phi i))
    atTop (𝓝 (dist a b)))

include phi hr hconv

/-- A finite net in the sample metric survives passage to the limit. -/
theorem sample_limit_cover (R k : ℕ) (a : s.Index)
    (ha : dist a none < (R:ℝ)+1) :
    ∃ j : Fin (s.size R k), dist a (some ⟨R,k,j⟩) ≤ 1/((k:ℝ)+1) := by
  by_contra hnot
  push Not at hnot
  have hlarge : ∀ᶠ i in atTop, ∀ j : Fin (s.size R k),
      1/((k:ℝ)+1) < dist (s.sample (phi i) a) (s.point (phi i) R k j) / r (phi i) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hconv a (some ⟨R,k,j⟩)).eventually (lt_mem_nhds (hnot j))
  have hnear : ∀ᶠ i in atTop,
      dist (s.sample (phi i) a) p / r (phi i) < (R:ℝ)+1 :=
    (hconv a none).eventually (gt_mem_nhds ha)
  obtain ⟨i, hi, hj⟩ := (hnear.and hlarge).exists
  obtain ⟨j, hsmall⟩ := s.covers (phi i) R k (s.sample (phi i) a)
    ((div_lt_iff₀ (hr (phi i))).mp hi).le
  have hh := (lt_div_iff₀ (hr (phi i))).mp (hj j)
  have heq : 1/((k:ℝ)+1)*r (phi i) = r (phi i)/((k:ℝ)+1) := by ring
  rw [heq] at hh
  exact (not_lt_of_ge hh.le) hsmall

/-- The completed limit has the same finite covers, with twice the mesh. -/
theorem completion_limit_cover (R k : ℕ)
    (y : UniformSpace.Completion s.Index)
    (hy : dist y (none : s.Index) ≤ R) :
    ∃ j : Fin (s.size R k),
      dist y ((some ⟨R,k,j⟩ : s.Index) : UniformSpace.Completion s.Index) <
        2/((k:ℝ)+1) := by
  have hsmall : 0 < min (1/((k:ℝ)+1)) (1/2:ℝ) := by positivity
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt y hsmall
  have hclose : dist y (a : UniformSpace.Completion s.Index) < 1/((k:ℝ)+1) :=
    ha.trans_le (min_le_left _ _)
  have hhalf : dist y (a : UniformSpace.Completion s.Index) < 1/2 :=
    ha.trans_le (min_le_right _ _)
  have habase : dist a (none : s.Index) < (R:ℝ)+1 := by
    rw [← UniformSpace.Completion.dist_eq]
    have hh := dist_triangle (a : UniformSpace.Completion s.Index) y (none : s.Index)
    rw [dist_comm (a : UniformSpace.Completion s.Index) y] at hh
    linarith only [hh, hy, hhalf]
  obtain ⟨j, hj⟩ := s.sample_limit_cover phi hr hconv R k a habase
  refine ⟨j, ?_⟩
  have hh := dist_triangle y (a : UniformSpace.Completion s.Index)
    ((some ⟨R,k,j⟩ : s.Index) : UniformSpace.Completion s.Index)
  rw [UniformSpace.Completion.dist_eq] at hh
  calc
    _ ≤ dist y (a : UniformSpace.Completion s.Index) + dist a (some ⟨R,k,j⟩) := hh
    _ < 1/((k:ℝ)+1) + 1/((k:ℝ)+1) := add_lt_add_of_lt_of_le hclose hj
    _ = _ := by ring

/-- Completing the sampled pseudometric gives a proper metric space. -/
theorem completion_proper : ProperSpace (UniformSpace.Completion s.Index) := by
  apply ProperSpace.of_seq_closedBall
    (x := ((none : s.Index) : UniformSpace.Completion s.Index))
    (r := fun k : ℕ => (k:ℝ)) tendsto_natCast_atTop_atTop
  apply Eventually.of_forall
  intro R
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_, isClosed_closedBall.isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro epsilon hepsilon
  have hlimit : Tendsto (fun k : ℕ => 2/((k:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  obtain ⟨k, hk⟩ := (hlimit.eventually (gt_mem_nhds hepsilon)).exists
  let center (j : Fin (s.size R k)) : UniformSpace.Completion s.Index :=
    (some ⟨R,k,j⟩ : s.Index)
  refine ⟨range center, finite_range center, ?_⟩
  intro y hy
  obtain ⟨j, hj⟩ := s.completion_limit_cover phi hr hconv R k y hy
  exact mem_iUnion₂.mpr ⟨center j, ⟨j,rfl⟩, hj.trans hk⟩

end RegularPointCoordinates.RescalingNetFamily

end

end OAI
