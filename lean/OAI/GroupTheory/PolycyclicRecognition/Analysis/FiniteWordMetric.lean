import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.Geometry.Group.WordMetric
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-! # The concrete word metrics used in the metric-free main statement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

theorem finite_lists_length_le (A : Type*) [Finite A] (n : ℕ) :
    {l : List A | l.length ≤ n}.Finite := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply ((Set.finite_singleton ([] : List A)).union
      ((Set.toFinite (Set.univ : Set A)).image2 List.cons ih)).subset
    intro l hl
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      exact Or.inr ⟨a, Set.mem_univ _, l, by simpa using hl, rfl⟩

namespace WordMetric

variable {G I : Type*} [Group G] (P : Group.Generators G I)

theorem dist_eq (x y : G) :
    letI := P.normedGroup
    dist x y = (P.wordLength (x⁻¹ * y) : ℝ) := rfl

theorem leftInvariant : letI := P.normedGroup; IsIsometricSMul G G := by
  let := P.normedGroup
  refine ⟨fun g => Isometry.of_dist_eq (fun x y => ?_)⟩
  simp only [smul_eq_mul, dist_eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem discrete : letI := P.normedGroup; DiscreteTopology G := by
  let := P.normedGroup
  apply DiscreteTopology.of_forall_le_dist (show (0 : ℝ) < 1 by norm_num)
  intro x y hxy
  rw [dist_eq]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    exact hxy (inv_mul_eq_one.mp (P.wordLength_eq_zero_iff.mp hzero)))

theorem finite_closedBall [Finite I] (x : G) (R : ℝ) :
    letI := P.normedGroup
    (closedBall x R).Finite := by
  let := P.normedGroup
  apply ((finite_lists_length_le (I × Bool) ⌈R⌉₊).image
    (fun l => x * P.wordProd l)).subset
  intro y hy
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l, ?_, by simp [he]⟩
  have hlen : (l.length : ℝ) ≤ R := by
    rw [mem_closedBall, dist_comm, dist_eq, ← he, hl.eq] at hy
    exact hy
  exact_mod_cast hlen.trans (Nat.le_ceil R)

theorem proper [Finite I] : letI := P.normedGroup; ProperSpace G :=
  by
    let := P.normedGroup
    exact ⟨fun x R => (finite_closedBall P x R).isCompact⟩

/-- Prefixes of a shortest representing word form a unit-step chain whose
length is the word distance. -/
def chains : letI := P.normedGroup; LinearMetricChains G := by
  let := P.normedGroup
  let := leftInvariant P
  refine {
    step := 1
    step_pos := by norm_num
    slope := 1
    slope_nonneg := by norm_num
    error := 0
    error_nonneg := by norm_num
    chain := ?_ }
  intro x y
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l.length, fun n => x * P.wordProd (l.take n), by simp, by simp [he], ?_, ?_⟩
  · rw [one_mul, add_zero, dist_eq, ← he, hl.eq]
  · intro i hi
    rw [dist_mul_left, dist_eq, ← List.take_concat_get' l i hi, P.wordProd_append,
      inv_mul_cancel_left]
    exact_mod_cast (P.wordLength_wordProd_le [l[i]] )

end WordMetric

/-- A finitely generated group admits the concrete proper, discrete word
metric and its linear chains, without an external metric-existence input. -/
theorem exists_finite_word_metric (G : Type*) [Group G] [Group.FG G] :
    ∃ d : MetricSpace G, letI := d
      DiscreteTopology G ∧ IsIsometricSMul G G ∧ ProperSpace G ∧
        Nonempty (LinearMetricChains G) := by
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG G)
  exact ⟨P.normedGroup.toMetricSpace, WordMetric.discrete P, WordMetric.leftInvariant P,
    WordMetric.proper P, ⟨WordMetric.chains P⟩⟩

end PolycyclicRecognition

end

end OAI
