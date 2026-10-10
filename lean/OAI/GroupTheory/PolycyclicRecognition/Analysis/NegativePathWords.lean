import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathRadius
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePackingAsymptotics

namespace OAI

/-! # Unit-step words remain in the negative halfspace

This is the concrete subdivision needed for quotient-boundary independence.
The logarithmic mesh error is absorbed into half of the negative height gap.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
/-- Integer points of an actual one-parameter subgroup lie in a linear
ball. This supplies the absolute radius of the negative-height ray pivots. -/
theorem one_parameter_nat_dist_le
    (d : ℝ → G) (hzero : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (n : ℕ) : dist 1 (d n) ≤ (n : ℝ) * dist 1 (d 1) := by
  have he : d (n : ℝ) = d 1 ^ n := by
    induction n with
    | zero => simpa only [Nat.cast_zero, pow_zero] using hzero
    | succ n ih => rw [Nat.cast_succ, hmul, ih, pow_succ]
  rw [he]
  exact dist_one_pow_le _ _

omit [IsTopologicalGroup G] in
/-- Retain the actual prefixes of an eventually specified unit-step word.
Their absolute radius follows by adding the radius of the starting point. -/
theorem exists_negative_word_prefix_chains
    (height : G → ℝ) (base target : ℕ → G) {C D gap : ℝ} {q : ℕ}
    (hbase : ∀ n : ℕ, dist 1 (base n) ≤ D * n)
    (hwords : ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧ w.prod = (base n)⁻¹ * target n ∧
      (w.length : ℝ) ≤ C * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (base n * (w.take i).prod) ≤ -gap * n ∧
        dist (base n) (base n * (w.take i).prod) ≤ C * n) :
    ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = base n) ∧
      (∀ᶠ n in atTop, z n (m n) = target n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ C * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, height (z n i) ≤ -gap * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ (D + C) * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  classical
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hwords
  let w : ℕ → List G := fun n => if hn : n₀ ≤ n then (hn₀ n hn).choose else []
  have hw (n : ℕ) (hn : n₀ ≤ n) :
      (∀ g ∈ w n, g ∈ closedBall (1 : G) 1) ∧ (w n).prod = (base n)⁻¹ * target n ∧
      ((w n).length : ℝ) ≤ C * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (base n * ((w n).take i).prod) ≤ -gap * n ∧
        dist (base n) (base n * ((w n).take i).prod) ≤ C * n := by
    simpa only [w, dite_eq_left hn] using (hn₀ n hn).choose_spec
  let z := fun n i => base n * ((w n).take i).prod
  refine ⟨fun n => (w n).length, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [z]
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    simp only [z, List.take_length, (hw n hn).2.1, mul_inv_cancel_left]
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (hw n hn).2.2.1
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact fun i _ => ((hw n hn).2.2.2 i).1
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    intro i _
    have htri := dist_triangle (1 : G) (base n) (z n i)
    have hi := ((hw n hn).2.2.2 i).2
    have hb := hbase n
    dsimp only [z] at htri ⊢
    linarith
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    intro i hi
    change dist (base n * ((w n).take i).prod) (base n * ((w n).take (i + 1)).prod) ≤ 1
    rw [List.prod_take_succ _ _ hi, dist_mul_left]
    have he : dist ((w n).take i).prod (((w n).take i).prod * (w n)[i]) =
        dist (1 : G) (w n)[i] := by
      simpa only [mul_one] using dist_mul_left ((w n).take i).prod (1 : G) (w n)[i]
    rw [he]
    simpa only [mem_closedBall, dist_comm] using (hw n hn).1 _ (List.getElem_mem hi)

/-- Subdivision can start at any point of the actual negative-height
path. Every resulting prefix stays nearby, has negative linear height,
and the number of unit steps is bounded by a fixed quadratic. -/
theorem eventually_negative_path_unit_words
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (height : G → ℝ) {K C a : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (ha : 0 < a)
    (hheight : ∀ x y, |height x - height y| ≤ K * dist x y)
    (source target : ℕ → G)
    (hγ : ∀ᶠ n : ℕ in atTop, ∃ γ : Path (source n) (target n),
      PathMetricBound γ (C * n) (C * (1 + Real.log (2 + n))) ∧
      ∀ t, height (γ t) ≤ -a * n) :
    ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ x ∈ w, x ∈ closedBall (1 : G) 1) ∧
      w.prod = (source n)⁻¹ * target n ∧
      (w.length : ℝ) ≤ (3 + (C + 1) * (3 * C + 2)) * (1 + n) ^ 2 ∧
      ∀ j : ℕ,
        height (source n * (w.take j).prod) ≤ -(a / 2) * n ∧
        dist (source n) (source n * (w.take j).prod) ≤ (7 * C + 2) * n := by
  have herr := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_logarithmic_error_le (K * C) (2 * K) (by positivity : 0 < a / 2))
  filter_upwards [hγ, herr, eventually_ge_atTop (1 : ℕ)] with n hn he hn1
  obtain ⟨γ, hmetric, hnegative⟩ := hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let η : Path (1 : G) ((source n)⁻¹ * target n) := {
    toFun := fun t => (source n)⁻¹ * γ t
    continuous_toFun := continuous_const.mul γ.continuous
    source' := by simp
    target' := by simp }
  have hη : PathMetricBound η (C * n) (C * (1 + Real.log (2 + n))) := by
    intro s t
    change dist ((source n)⁻¹ * γ s) ((source n)⁻¹ * γ t) ≤ _
    rw [dist_mul_left]
    exact hmetric s t
  have hlog0 : 0 ≤ 1 + Real.log (2 + (n : ℝ)) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2 + (n : ℝ))
    linarith
  obtain ⟨w, hw, hp, hlen, hnear⟩ := exists_word_near_coarse_path hpath η
    (mul_nonneg hC hn0) (mul_nonneg hC hlog0) hη
  have hpref := coarse_path_word_prefactor_le hC hn1'
  refine ⟨w, hw, hp, by linarith, ?_⟩
  intro j
  obtain ⟨t, ht⟩ := hnear j
  have hdist : dist (source n * (w.take j).prod) (γ t) ≤
      C * (1 + Real.log (2 + n)) + 2 := by
    have hh := dist_mul_left (source n) (w.take j).prod (η t)
    change dist (source n * (w.take j).prod) (source n * ((source n)⁻¹ * γ t)) = _ at hh
    rw [mul_inv_cancel_left] at hh
    rwa [hh]
  constructor
  · have hdiff := (hheight (source n * (w.take j).prod) (γ t)).trans
      (mul_le_mul_of_nonneg_left hdist hK)
    have hsigned := (le_abs_self (height (source n * (w.take j).prod) - height (γ t))).trans hdiff
    have hnneg := hnegative t
    nlinarith
  · have hrad := hmetric.dist_source_le_linear hC hn1' t
    have hlog : 1 + Real.log (2 + (n : ℝ)) ≤ 3 * n := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + (n : ℝ))
      linarith
    have hh := mul_le_mul_of_nonneg_left hlog hC
    have htri := dist_triangle (source n) (γ t) (source n * (w.take j).prod)
    rw [dist_comm (γ t)] at htri
    linarith

end PolycyclicRecognition

end

end OAI
