import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Find

namespace OAI

/-!
# Counting separated endpoints using Haar volume

Disjoint fixed-radius balls around separated endpoints have the same positive
Haar mass. A polynomial-volume region containing their thickening therefore
gives a polynomial cardinal bound. This is the counting step of the path
packing lemma, separated from its Lie-coordinate estimate.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G]

omit [BorelSpace G] in
theorem measure_ball_eq_identity (μ : Measure G) [IsMulLeftInvariant μ]
    (x : G) (r : ℝ) : μ (ball x r) = μ (ball (1 : G) r) := by
  have h := measure_preimage_mul μ x (ball x r)
  rw [preimage_mul_left_ball, inv_mul_cancel] at h
  exact h.symm

/-- The Haar volume of a thickening bounds the number of separated centers. -/
theorem separated_card_mul_ball_le (μ : Measure G) [IsMulLeftInvariant μ]
    (s : Finset G) (r : ℝ) (region : Set G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ dist x y)
    (hthick : ∀ x ∈ s, ball x r ⊆ region) :
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) ≤ μ region := by
  classical
  have hd : Set.Pairwise (s : Set G) (fun x y => Disjoint (ball x r) (ball y r)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (hsep x hx y hy hxy)
  calc
    (s.card : ℝ≥0∞) * μ (ball (1 : G) r) = μ (⋃ x ∈ s, ball x r) := by
      rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)]
      simp only [measure_ball_eq_identity, Finset.sum_const, nsmul_eq_mul]
    _ ≤ μ region := measure_mono (iUnion₂_subset hthick)

/-- A polynomial Haar-volume upper bound becomes a polynomial bound on every
finite separated subset. The ball mass is canceled with its nonzero/finite
hypotheses explicit. -/
theorem separated_card_le_polynomial (μ : Measure G) [IsMulLeftInvariant μ]
    (s : Finset G) (r : ℝ) (region : Set G) (C b t : ℕ)
    (hq0 : μ (ball (1 : G) r) ≠ 0) (hqtop : μ (ball (1 : G) r) ≠ ⊤)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ dist x y)
    (hthick : ∀ x ∈ s, ball x r ⊆ region)
    (hvol : μ region ≤ ((C * (1 + t) ^ b : ℕ) : ℝ≥0∞) * μ (ball (1 : G) r)) :
    s.card ≤ C * (1 + t) ^ b := by
  have h := (separated_card_mul_ball_le μ s r region hsep hthick).trans hvol
  have hh : (s.card : ℝ≥0∞) ≤ ((C * (1 + t) ^ b : ℕ) : ℝ≥0∞) :=
    (ENNReal.mul_le_mul_iff_left hq0 hqtop).mp h
  exact_mod_cast hh

/-- A cardinal bound on separated subsets gives a finite cover of the original
finite set. Endpoint sets need not be measurable. -/
theorem finite_cover_of_separated_bound {X : Type*} [PseudoMetricSpace X]
    (s : Finset X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, t ⊆ s →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, t ⊆ s ∧ t.card ≤ N ∧
      ∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P := s.powerset.filter fun t => ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y
  have hP : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image P Finset.card hP
  obtain ⟨hts, hsep⟩ : t ⊆ s ∧ (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) := by
    simpa only [P, Finset.mem_filter, Finset.mem_powerset] using ht
  refine ⟨t, hts, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    have := hfar x hxt
    simp only [dist_self] at this
    exact (not_lt_of_ge hr) this
  have hinsert : insert x t ∈ P := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hts), ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have hcard := hmax (insert x t) hinsert
  rw [Finset.card_insert_of_notMem hxt] at hcard
  omega

/-- The same maximal-packing argument applies to arbitrary endpoint sets. A
bound on their finite separated subsets already supplies a finite net; no
measurability or compactness of the endpoint set is needed. -/
theorem finite_separated_cover_set_of_bound {X : Type*} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  classical
  let P (k : ℕ) := ∃ t : Finset X, (↑t : Set X) ⊆ S ∧
    (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) ∧ t.card = k
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨t, hts, hsep, hcard⟩ := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hmax (u : Finset X) (hu : (↑u : Set X) ⊆ S)
      (husep : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → r < dist x y) : u.card ≤ t.card := by
    rw [hcard]
    exact Nat.le_findGreatest (hbound u hu husep) ⟨u, hu, husep, rfl⟩
  refine ⟨t, hts, hsep, hbound t hts hsep, ?_⟩
  intro x hx
  by_contra hno
  have hfar : ∀ y ∈ t, r < dist x y := by
    intro y hy
    exact lt_of_not_ge (fun h => hno ⟨y, hy, h⟩)
  have hxt : x ∉ t := by
    intro hxt
    exact (not_lt_of_ge hr) (by simpa only [dist_self] using hfar x hxt)
  have hins : (↑(insert x t) : Set X) ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hyt
    · exact hxy ▸ hx
    · exact hts hyt
  have hsepins : ∀ a ∈ insert x t, ∀ b ∈ insert x t, a ≠ b → r < dist a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | hat
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbt
      · exact (hab hbx.symm).elim
      · exact hfar b hbt
    · rcases Finset.mem_insert.mp hb with hbx | hbt
      · subst b
        simpa only [dist_comm] using hfar a hat
      · exact hsep a hat b hbt hab
  have h := hmax (insert x t) hins hsepins
  rw [Finset.card_insert_of_notMem hxt] at h
  omega

/-- Retain the covering conclusion when separation of the centers is not needed. -/
theorem finite_cover_set_of_separated_bound {X : Type*} [PseudoMetricSpace X]
    (S : Set X) {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (hbound : ∀ t : Finset X, (↑t : Set X) ⊆ S →
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → r < dist x y) → t.card ≤ N) :
    ∃ t : Finset X, (↑t : Set X) ⊆ S ∧ t.card ≤ N ∧
      ∀ x ∈ S, ∃ y ∈ t, dist x y ≤ r := by
  obtain ⟨t, ht, _hsep, hcard, hcover⟩ := finite_separated_cover_set_of_bound S hr N hbound
  exact ⟨t, ht, hcard, hcover⟩

end PolycyclicRecognition

end OAI
