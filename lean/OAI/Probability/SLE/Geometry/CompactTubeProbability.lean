import Mathlib
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

namespace OAI

/-! A finite-cover argument makes individual tube probabilities uniform on
a compact family of routes. No quantitative support estimate is assumed. -/

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SLEExactGauge

theorem finite_positive_lower_bound {X : Type*} (S : Set X) (hS : S.Finite)
    (f : X → ℝ≥0∞) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ x ∈ S, q ≤ f x := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x S hx hS ih =>
    obtain ⟨q, hq, hbound⟩ := ih (fun y hy => hf y (mem_insert_of_mem x hy))
    refine ⟨min (f x) q, lt_min (hf x (mem_insert x S)) hq, ?_⟩
    intro y hy
    rcases mem_insert_iff.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound y hy)

/-- Pointwise positivity on half-radius balls gives one positive lower
bound for full-radius balls centered anywhere in a compact set. -/
theorem compact_tube_probability_lower_bound
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (P : Measure X) (K : Set X) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hpositive : ∀ x ∈ K, 0 < P (ball x (ε / 2))) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ x ∈ K, q ≤ P (ball x ε) := by
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls (half_pos hε)
  obtain ⟨q, hq, hbound⟩ := finite_positive_lower_bound S hS
    (fun x => P (ball x (ε / 2))) (fun x hx => hpositive x (hSK hx))
  refine ⟨q, hq, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  refine (hbound y hy).trans (measure_mono ?_)
  intro z hz
  have hd := dist_triangle z y x
  have hxy' : dist y x < ε / 2 := by simpa only [mem_ball, dist_comm] using hxy
  have hzy : dist z y < ε / 2 := hz
  change dist z x < ε
  linarith

end SLEExactGauge

namespace SLEExactGauge.CompactRouteTubes

local instance compactRouteMeasurableSpace : MeasurableSpace (unitInterval →ᵇ ℂ) := borel _
local instance compactRouteBorelSpace : BorelSpace (unitInterval →ᵇ ℂ) := ⟨rfl⟩

/-- The usual pointwise full-support statement for continuous paths based
at zero is enough for a uniform tube probability over all routes with a
fixed speed bound. Arzela--Ascoli and a finite cover supply the uniformity. -/
theorem uniform_tube_probability_of_based_support
    (P : Measure (unitInterval →ᵇ ℂ)) (C : ℝ≥0) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ f : unitInterval →ᵇ ℂ, f 0 = 0 → ∀ r : ℝ, 0 < r →
      0 < P (ball f r)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ f : unitInterval →ᵇ ℂ,
      LipschitzWith C f → f 0 = 0 →
      q ≤ P {g | ∀ t : unitInterval, dist (g t) (f t) < ε} := by
  let S : Set (unitInterval →ᵇ ℂ) := {f | LipschitzWith C f ∧ f 0 = 0}
  have heq : Equicontinuous ((↑) : S → unitInterval → ℂ) := by
    apply (LipschitzWith.uniformEquicontinuous _ C ?_).equicontinuous
    intro f
    exact f.property.1
  have hbound : ∀ f ∈ S, ∀ t : unitInterval, f t ∈ closedBall (0 : ℂ) C := by
    intro f hf t
    have hh := hf.1.dist_le_mul t 0
    have ht : dist t (0 : unitInterval) ≤ 1 := by
      change |(t : ℝ) - 0| ≤ 1
      simpa only [sub_zero, abs_of_nonneg t.property.1] using t.property.2
    rw [hf.2] at hh
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht C.coe_nonneg)
  have hcompact : IsCompact (closure S) := BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ) C) (isCompact_closedBall _ _) S (fun f t hf => hbound f hf t) heq
  have hbasedClosed : IsClosed {f : unitInterval →ᵇ ℂ | f 0 = 0} :=
    isClosed_eq (BoundedContinuousFunction.lipschitz_eval_const 0).continuous continuous_const
  have hbased : closure S ⊆ {f : unitInterval →ᵇ ℂ | f 0 = 0} :=
    closure_minimal (fun _ hf => hf.2) hbasedClosed
  obtain ⟨q, hq, hqbound⟩ := compact_tube_probability_lower_bound P (closure S) hcompact hε
    (fun f hf => hsupport f (hbased hf) (ε / 2) (half_pos hε))
  refine ⟨q, hq, ?_⟩
  intro f hf hf0
  refine (hqbound f (subset_closure ⟨hf, hf0⟩)).trans (measure_mono ?_)
  intro g hg t
  exact (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hg

end SLEExactGauge.CompactRouteTubes

end

end OAI
