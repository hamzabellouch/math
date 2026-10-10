import OAI.GroupTheory.PolycyclicRecognition.Analysis.NegativePathWords

namespace OAI

/-! # Polynomially subdivided paths at negative height -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric Set
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

/-- A polynomial coarse speed with a constant mesh error suffices for
polynomially many unit steps. Negative linear height survives subdivision. -/
theorem polynomial_negative_path_chains
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (height : G → ℝ) {K C R a : ℝ} {q : ℕ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : 0 < a)
    (hheight : ∀ x y, |height x - height y| ≤ K * dist x y)
    (source target : ℕ → G)
    (hsource : ∀ n, dist 1 (source n) ≤ R * n)
    (hγ : ∀ᶠ n : ℕ in atTop, ∃ γ : Path (source n) (target n),
      PathMetricBound γ (C * (1 + n) ^ q) C ∧
      (∀ t, height (γ t) ≤ -a * n) ∧ (∀ t, dist 1 (γ t) ≤ R * n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ (m : ℕ → ℕ) (z : ℕ → ℕ → G),
      (∀ n, z n 0 = source n) ∧
      (∀ᶠ n in atTop, z n (m n) = target n) ∧
      (∀ᶠ n in atTop, (m n : ℝ) ≤ B * (1 + n) ^ q) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, height (z n i) ≤ -(a / 2) * n) ∧
      (∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ B * n) ∧
      ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1 := by
  let B := (C + 1) * (C + 2) + 3 * R + C + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have herr : ∀ᶠ n : ℕ in atTop, K * (C + 2) ≤ (a / 2) * n := by
    have ht : Tendsto (fun n : ℕ => (a / 2) * (n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
        (by linarith)
    exact ht.eventually (eventually_ge_atTop _)
  have hwords : ∀ᶠ n : ℕ in atTop, ∃ w : List G,
      (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧
      w.prod = (source n)⁻¹ * target n ∧
      (w.length : ℝ) ≤ (B - R) * (1 + n) ^ q ∧ ∀ i : ℕ,
        height (source n * (w.take i).prod) ≤ -(a / 2) * n ∧
        dist (source n) (source n * (w.take i).prod) ≤ (B - R) * n := by
    filter_upwards [hγ, herr, eventually_ge_atTop (1 : ℕ)] with n hn he hn1
    obtain ⟨γ, hmetric, hnegative, hradius⟩ := hn
    let η : Path (1 : G) ((source n)⁻¹ * target n) := {
      toFun := fun t => (source n)⁻¹ * γ t
      continuous_toFun := continuous_const.mul γ.continuous
      source' := by simp
      target' := by simp }
    have hη : PathMetricBound η (C * (1 + n) ^ q) C := by
      intro s t
      change dist ((source n)⁻¹ * γ s) ((source n)⁻¹ * γ t) ≤ _
      rw [dist_mul_left]
      exact hmetric s t
    obtain ⟨w, hw, hp, hlen, hnear⟩ := exists_word_near_coarse_path hpath η
      (by positivity) hC hη
    have hpow : 1 ≤ (1 + (n : ℝ)) ^ q := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hcoef : (C + 1) * (C + 2) ≤ B - R := by dsimp [B]; nlinarith
    refine ⟨w, hw, hp, hlen.trans ?_, ?_⟩
    · calc
        (C * (1 + (n : ℝ)) ^ q + 1) * (C + 2) ≤
            ((C + 1) * (1 + (n : ℝ)) ^ q) * (C + 2) := by gcongr; nlinarith
        _ = ((C + 1) * (C + 2)) * (1 + (n : ℝ)) ^ q := by ring
        _ ≤ (B - R) * (1 + (n : ℝ)) ^ q := by gcongr
    · intro i
      obtain ⟨t, ht⟩ := hnear i
      have hdist : dist (source n * (w.take i).prod) (γ t) ≤ C + 2 := by
        have hh := dist_mul_left (source n) (w.take i).prod (η t)
        change dist (source n * (w.take i).prod) (source n * ((source n)⁻¹ * γ t)) = _ at hh
        rw [mul_inv_cancel_left] at hh
        rwa [hh]
      constructor
      · have hsigned := (le_abs_self (height (source n * (w.take i).prod) - height (γ t))).trans
          ((hheight _ _).trans (mul_le_mul_of_nonneg_left hdist hK))
        have hneg := hnegative t
        nlinarith
      · have hs := hsource n
        have hr := hradius t
        have htri := dist_triangle (source n) (γ t) (source n * (w.take i).prod)
        have hrad := dist_triangle (source n) (1 : G) (γ t)
        rw [dist_comm (γ t)] at htri
        rw [dist_comm (source n) (1 : G)] at hrad
        have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hCR : 0 ≤ C + 2 := by linarith
        have hh := mul_le_mul_of_nonneg_left hn1' hCR
        have hcoeff : 2 * R + C + 2 ≤ B - R := by dsimp [B]; nlinarith
        have hh' := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) n)
        nlinarith
  obtain ⟨m, z, hz0, hzend, hlen, hheight', hball, hsteps⟩ :=
    exists_negative_word_prefix_chains height source target hsource hwords
  refine ⟨B, hB, m, z, hz0, hzend, ?_, hheight', ?_, hsteps⟩
  · filter_upwards [hlen] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · filter_upwards [hball] with n hn
    simpa only [add_sub_cancel] using hn

end PolycyclicRecognition

end

end OAI
