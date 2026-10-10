import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledChainWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation

namespace OAI

/-! # Subdividing coarse paths into bounded-increment words

A path with speed `L` and additive error `κ` admits a unit-step word of
length at most `(L + 1) * (κ + 2)`. Its prefixes remain within `κ + 2` of
points on the path. In the application `L = O(r)` and `κ = O(log r)`, so this
loss is polynomial and its extra height error is sublinear.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- The uniform subdivision of the unit interval, constant after its endpoint. -/
def subdivisionPoint (n : ℕ) (hn : 0 < n) (i : ℕ) : unitInterval :=
  ⟨((min i n : ℕ) : ℝ) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · positivity
    · exact (div_le_one hn').mpr (by exact_mod_cast Nat.min_le_right i n)⟩

@[simp] theorem subdivisionPoint_coe (n : ℕ) (hn : 0 < n) {i : ℕ} (hi : i ≤ n) :
    (subdivisionPoint n hn i : ℝ) = (i : ℝ) / n := by
  simp only [subdivisionPoint, Nat.min_eq_left hi]

@[simp] theorem subdivisionPoint_zero (n : ℕ) (hn : 0 < n) :
    subdivisionPoint n hn 0 = 0 := by
  apply Subtype.ext
  simp

@[simp] theorem subdivisionPoint_self (n : ℕ) (hn : 0 < n) :
    subdivisionPoint n hn n = 1 := by
  apply Subtype.ext
  simp [ne_of_gt hn]

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A coarse path has a polynomially controlled unit-step word, with every
prefix close to an actual point on that same path. -/
theorem exists_word_near_coarse_path
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {g : G} (γ : Path (1 : G) g) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hγ : PathMetricBound γ L κ) :
    ∃ w : List G, (∀ x ∈ w, x ∈ closedBall (1 : G) 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ (L + 1) * (κ + 2) ∧
      ∀ j : ℕ, ∃ t : unitInterval, dist (w.take j).prod (γ t) ≤ κ + 2 := by
  let n := ⌊L⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hLn : L ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one L).le
  have hnL : (n : ℝ) ≤ L + 1 := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (add_le_add (Nat.floor_le hL) (show (1 : ℝ) ≤ 1 from le_rfl))
  let v : ℕ → G := fun i => γ (subdivisionPoint n hn i)
  have hv0 : v 0 = 1 := by simp [v]
  have hvn : v n = g := by simp [v]
  have hstep (i : ℕ) (hi : i < n) : dist (v i) (v (i + 1)) ≤ 1 + κ := by
    have hdiff : |(i : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right
        (by exact_mod_cast Nat.le_succ i) hn'.le))]
      push_cast
      ring
    calc
      _ ≤ L * |(subdivisionPoint n hn i : ℝ) - subdivisionPoint n hn (i + 1)| + κ := hγ _ _
      _ = L / n + κ := by
        rw [subdivisionPoint_coe n hn hi.le,
          subdivisionPoint_coe n hn (Nat.succ_le_of_lt hi), hdiff, mul_one_div]
      _ ≤ 1 + κ := add_le_add ((div_le_one hn').mpr hLn) le_rfl
  obtain ⟨w, hw, hprod, hlen, hnear⟩ := exists_word_near_chain hpath v hv0
    (show 0 ≤ 1 + κ by linarith) n hstep
  refine ⟨w, hw, hprod.trans hvn, ?_, ?_⟩
  · calc
      (w.length : ℝ) ≤ (n : ℝ) * (κ + 2) := by convert hlen using 1; ring
      _ ≤ (L + 1) * (κ + 2) := mul_le_mul_of_nonneg_right hnL (by linarith)
  · intro j
    obtain ⟨i, _, hi⟩ := hnear j
    exact ⟨subdivisionPoint n hn i, by convert hi using 1; ring⟩

end PolycyclicRecognition

end

end OAI
