import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricCoarseBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.Geometry.Group.WordMetric
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-! # Finite balls for the actual word metric

Mathlib constructs a normed group from a generating family. A finite family
has only finitely many words of bounded length, so this metric supplies the
finite-ball hypothesis used in the recognition and lattice comparison.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- There are finitely many words of bounded length over a finite alphabet. -/
theorem finite_bounded_length_lists (A : Type*) [Finite A] (n : ℕ) :
    {l : List A | l.length ≤ n}.Finite := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hc := ((Set.toFinite (univ : Set A)).prod ih).image
      (fun p : A × List A => p.1 :: p.2)
    apply ((Set.finite_singleton ([] : List A)).union hc).subset
    intro l hl
    cases l with
    | nil => exact Or.inl (mem_singleton _)
    | cons a l =>
      right
      exact ⟨(a, l), ⟨mem_univ a, by simpa using hl⟩, rfl⟩

variable {G ι : Type*} [Group G]

/-- The group elements of bounded word length form a finite set. -/
theorem finite_wordLength_ball [Finite ι] (P : Group.Generators G ι) (n : ℕ) :
    {g : G | P.wordLength g ≤ n}.Finite := by
  apply ((finite_bounded_length_lists (ι × Bool) n).image P.wordProd).subset
  intro g hg
  obtain ⟨l, hl, hlg⟩ := (P.wordLength_le_iff g).mp hg
  exact ⟨l, hl, hlg⟩

/-- The normed group built from a finite generating family has finite
closed balls. -/
theorem finite_wordMetric_closedBall [Finite ι] (P : Group.Generators G ι) :
    letI := P.normedGroup
    ∀ R : ℝ, (closedBall (1 : G) R).Finite := by
  let := P.normedGroup
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  apply (finite_wordLength_ball P n).subset
  intro g hg
  have hgR : (P.wordLength g : ℝ) ≤ R := by
    have hg' := mem_closedBall.mp hg
    change (P.wordLength (g⁻¹ * 1) : ℝ) ≤ R at hg'
    simpa only [mul_one, Group.Generators.wordLength_inv] using hg'
  exact_mod_cast hgR.trans hn

/-- Finite generation supplies a finite generating family whose actual
Mathlib word metric has finite closed balls. -/
theorem exists_finite_wordMetric [Group.FG G] :
    ∃ (n : ℕ) (P : Group.Generators G (Fin n)),
      letI := P.normedGroup
      ∀ R : ℝ, (closedBall (1 : G) R).Finite := by
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp
    (inferInstance : Group.FG G)
  exact ⟨n, P, finite_wordMetric_closedBall P⟩

/-- The actual word metric is proper because every translated closed ball
is finite. -/
theorem proper_wordMetric [Finite ι] (P : Group.Generators G ι) :
    letI := P.normedGroup
    ProperSpace G := by
  let := P.normedGroup
  refine ⟨fun x R => ?_⟩
  apply Set.Finite.isCompact
  apply ((finite_wordMetric_closedBall P R).image (fun y : G => x * y)).subset
  intro y hy
  refine ⟨x⁻¹ * y, ?_, by simp⟩
  have hd : dist (x⁻¹ * y) 1 = dist y x := by
    simpa only [mul_inv_cancel_left, mul_one] using (dist_mul_left x (x⁻¹ * y) 1).symm
  simpa only [mem_closedBall, hd] using hy

/-- Distinct points have positive integral word distance, so every
singleton is open in the word metric. -/
theorem discrete_wordMetric (P : Group.Generators G ι) :
    letI := P.normedGroup
    DiscreteTopology G := by
  let := P.normedGroup
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  apply Metric.isOpen_singleton_iff.mpr
  refine ⟨1, zero_lt_one, fun y hy => ?_⟩
  change (P.wordLength (y⁻¹ * x) : ℝ) < 1 at hy
  have hnat : P.wordLength (y⁻¹ * x) < 1 := by exact_mod_cast hy
  have hn : P.wordLength (y⁻¹ * x) = 0 := Nat.lt_one_iff.mp hnat
  have heq : y⁻¹ * x = 1 := P.wordLength_eq_zero_iff.mp hn
  exact inv_mul_eq_one.mp heq

/-- Prefixes of a shortest representing word give unit-step chains of
length exactly the word-metric distance. -/
def wordMetric_linearChains (P : Group.Generators G ι) :
    letI := P.normedGroup
    LinearMetricChains G := by
  let := P.normedGroup
  refine {
    step := 1
    step_pos := by norm_num
    slope := 1
    slope_nonneg := by norm_num
    error := 0
    error_nonneg := le_rfl
    chain := ?_ }
  intro x y
  obtain ⟨l, hl, hprod⟩ := P.exists_isGeodesic (x⁻¹ * y)
  let p : ℕ → G := fun i => x * P.wordProd (l.take i)
  refine ⟨l.length, p, ?_, ?_, ?_, ?_⟩
  · simp [p]
  · simp [p, hprod]
  · have hn : (l.length : ℝ) = dist x y := by
      change (l.length : ℝ) = (P.wordLength (x⁻¹ * y) : ℝ)
      rw [← hprod, hl.eq]
    simp only [one_mul, add_zero, hn, le_refl]
  · intro i hi
    change dist (x * P.wordProd (l.take i)) (x * P.wordProd (l.take (i + 1))) ≤ 1
    rw [dist_mul_left, List.take_succ_eq_append_getElem hi, P.wordProd_append]
    have hd : dist (P.wordProd (l.take i))
        (P.wordProd (l.take i) * P.wordProd [l[i]]) = dist 1 (P.wordProd [l[i]]) := by
      simpa only [mul_one] using dist_mul_left (P.wordProd (l.take i)) 1 (P.wordProd [l[i]])
    rw [hd]
    change (P.wordLength (1⁻¹ * P.wordProd [l[i]]) : ℝ) ≤ 1
    simp only [inv_one, one_mul]
    exact_mod_cast (P.wordLength_wordProd_le [l[i]])

end PolycyclicRecognition

end

end OAI
