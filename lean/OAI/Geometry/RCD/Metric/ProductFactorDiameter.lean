import OAI.Geometry.RCD.Metric.ExtraFactorObstruction
import Mathlib.Analysis.Normed.Lp.ProdLp

namespace OAI

/-!
# The residual factor of a full-dimensional product approximation is small

An orthogonal simplex in the Euclidean factor together with one point in the
other factor gives an explicit dimension obstruction. This is the geometric
bridge needed after the product conclusion of Huang--Huang Theorem 2.9(2).
-/

open Metric

noncomputable section

namespace RegularPointCoordinates

private theorem metric_prod_dist_L2 {A Z : Type*} [MetricSpace A] [MetricSpace Z]
    (x y : WithLp 2 (A × Z)) :
    dist x y = Real.sqrt (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  have h := WithLp.prod_dist_eq_add (p := 2) (by norm_num) x y
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow] using h

private theorem scaled_unit_dist_zero (n : ℕ) (i : Fin n) {a : ℝ} (ha : 0 ≤ a) :
    dist (a • EuclideanSpace.single i (1 : ℝ)) (0 : Euclidean n) = a := by
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg ha]
  simp

private theorem scaled_units_dist (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    {a : ℝ} (ha : 0 ≤ a) :
    dist (a • EuclideanSpace.single i (1 : ℝ)) (a • EuclideanSpace.single j 1) =
      Real.sqrt 2 * a := by
  rw [dist_smul₀, Real.norm_of_nonneg ha]
  have hs : dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) =
      Real.sqrt 2 := by
    have he : dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real]
      norm_num [EuclideanSpace.inner_single_left, hij]
    have he' := Real.sqrt_sq (dist_nonneg : 0 ≤ dist
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1))
    rw [he] at he'
    exact he'.symm
  rw [hs, mul_comm]

/-- Points of the residual factor inside the unit ball must be close to
its base point when the same ball also approximates R^n. -/
theorem product_factor_distance_le {X Z : Type*} [MetricSpace X] [MetricSpace Z]
    (n : ℕ) {p : X} {z₀ z : Z} {r δ η : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hz : dist z z₀ ≤ 1)
    (f : X → Euclidean n) (g : X → WithLp 2 (Euclidean n × Z))
    (hf : IsPointedApproximation p 0 r 2 δ f)
    (hg : IsPointedApproximation p (WithLp.toLp 2 (0, z₀)) r 2 η g) :
    dist z z₀ ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) := by
  let a := dist z z₀
  have ha0 : 0 ≤ a := dist_nonneg
  by_cases ha : a = 0
  · rw [show dist z z₀ = 0 from ha]
    positivity
  have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
  let v : Fin (n + 1) → WithLp 2 (Euclidean n × Z) :=
    Fin.cases (WithLp.toLp 2 (0, z))
      (fun i => WithLp.toLp 2 (a • EuclideanSpace.single i 1, z₀))
  have hv (i) : dist (v i) (WithLp.toLp 2 (0, z₀)) = a := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change dist (WithLp.toLp 2 ((0 : Euclidean n), z)) (WithLp.toLp 2 (0, z₀)) = a
      rw [metric_prod_dist_L2]
      simp only [WithLp.fst, WithLp.snd, dist_self]
      change Real.sqrt ((0 : ℝ) ^ 2 + a ^ 2) = a
      norm_num [Real.sqrt_sq ha0]
    · change dist (WithLp.toLp 2 (a • EuclideanSpace.single j (1 : ℝ), z₀))
        (WithLp.toLp 2 (0, z₀)) = a
      rw [metric_prod_dist_L2]
      simp only [WithLp.fst, WithLp.snd, dist_self]
      change Real.sqrt (dist (a • EuclideanSpace.single j (1 : ℝ)) (0 : Euclidean n) ^ 2 + 0 ^ 2) = a
      rw [scaled_unit_dist_zero n j ha0]
      norm_num [Real.sqrt_sq ha0]
  have hp (i j) (hij : i ≠ j) : dist (v i) (v j) = Real.sqrt 2 * a := by
    have hextra (k : Fin n) : dist (v 0) (v k.succ) = Real.sqrt 2 * a := by
      change dist (WithLp.toLp 2 ((0 : Euclidean n), z))
        (WithLp.toLp 2 (a • EuclideanSpace.single k (1 : ℝ), z₀)) = _
      rw [metric_prod_dist_L2]
      simp only [WithLp.fst, WithLp.snd]
      change Real.sqrt (dist (0 : Euclidean n) (a • EuclideanSpace.single k (1 : ℝ)) ^ 2 + a ^ 2) = _
      rw [dist_comm (0 : Euclidean n), scaled_unit_dist_zero n k ha0]
      rw [show a ^ 2 + a ^ 2 = 2 * a ^ 2 by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq ha0]
    revert hij
    revert j
    refine Fin.cases ?_ (fun k => ?_) i
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · intro h
        exact (h rfl).elim
      · intro _
        exact hextra l
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · intro _
        rw [dist_comm]
        exact hextra k
      · intro hij
        have hkl : k ≠ l := fun h => hij (congrArg Fin.succ h)
        change dist (WithLp.toLp 2 (a • EuclideanSpace.single k (1 : ℝ), z₀))
          (WithLp.toLp 2 (a • EuclideanSpace.single l 1, z₀)) = _
        rw [metric_prod_dist_L2]
        simp only [WithLp.fst, WithLp.snd, dist_self]
        change Real.sqrt (dist (a • EuclideanSpace.single k (1 : ℝ))
          (a • EuclideanSpace.single l 1) ^ 2 + (0 : ℝ) ^ 2) = _
        norm_num only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
        rw [Real.sqrt_sq dist_nonneg]
        exact scaled_units_dist n k l hkl ha0
  exact simplex_approximation_obstruction n hr hδ hη hapos (by linarith)
    f g v hv hp hf hg

private theorem metric_prod_dist_error {A Z : Type*} [MetricSpace A] [MetricSpace Z]
    (x y : WithLp 2 (A × Z)) : |dist x y - dist x.fst y.fst| ≤ dist x.snd y.snd := by
  have hlo := WithLp.dist_fst_le x y
  have hup : dist x y ≤ dist x.fst y.fst + dist x.snd y.snd := by
    rw [metric_prod_dist_L2]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [dist_nonneg (x := x.fst) (y := y.fst),
        dist_nonneg (x := x.snd) (y := y.snd)]
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem metric_prod_same_second {A Z : Type*} [MetricSpace A] [MetricSpace Z]
    (a b : A) (z : Z) :
    dist (WithLp.toLp 2 (a, z)) (WithLp.toLp 2 (b, z)) = dist a b := by
  rw [metric_prod_dist_L2]
  simp only [WithLp.fst, WithLp.snd, dist_self]
  norm_num [Real.sqrt_sq dist_nonneg]

/-- Projection of a full-dimensional product approximation is itself a
pointed Euclidean approximation on the inner half-ball. -/
theorem product_projection_approximation {X Z : Type*} [MetricSpace X] [MetricSpace Z]
    (n : ℕ) {p : X} {z₀ : Z} {r δ η : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (f : X → Euclidean n) (g : X → WithLp 2 (Euclidean n × Z))
    (hf : IsPointedApproximation p 0 r 2 δ f)
    (hg : IsPointedApproximation p (WithLp.toLp 2 (0, z₀)) r 2 η g) :
    IsPointedApproximation p 0 r (1 / 2)
      (η + 20 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η)) (fun x => (g x).fst) := by
  let B := 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η)
  let ε := η + 2 * B
  have hεeq : η + 20 * ((n + 1 : ℕ) : ℝ) ^ 2 * (δ + 3 * η) = ε := by
    dsimp [ε, B]
    ring
  rw [hεeq]
  have hηB : η ≤ B := by
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hc : 1 ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    dsimp [B]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1)
      (by linarith : 0 ≤ δ + 3 * η)]
  have hε : η ≤ ε := by dsimp [ε]; linarith
  have hε3 : 3 * η ≤ ε := by dsimp [ε]; linarith
  have hlarge {x : X} (hx : dist x p ≤ 1 / 2 * r) : dist x p ≤ 2 * r := by nlinarith
  have hpp : dist p p ≤ 2 * r := by simp only [dist_self]; positivity
  have hzbound {x : X} (hx : dist x p ≤ 1 / 2 * r) : dist (g x).snd z₀ ≤ B := by
    have hdist := (abs_le.mp (hg.2.1 x p (hlarge hx) hpp)).2
    have hfirst : dist (g x).snd z₀ ≤ dist (g x) (WithLp.toLp 2 (0, z₀)) :=
      WithLp.dist_snd_le (g x) (WithLp.toLp 2 (0, z₀))
    have htri := dist_triangle (g x) (g p) (WithLp.toLp 2 (0, z₀))
    have hquot : dist x p / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr hx
    have hzunit : dist (g x).snd z₀ ≤ 1 := by linarith [hg.1]
    exact product_factor_distance_le n hr hδ hη (by linarith) hzunit f g hf hg
  refine ⟨(WithLp.dist_fst_le _ _).trans (hg.1.trans hε), ?_, ?_⟩
  · intro x y hx hy
    have hraw := hg.2.1 x y (hlarge hx) (hlarge hy)
    have hprod := metric_prod_dist_error (g x) (g y)
    have hz := dist_triangle (g x).snd z₀ (g y).snd
    have hz' : dist (g x).snd (g y).snd ≤ 2 * B := by
      rw [dist_comm z₀ (g y).snd] at hz
      linarith [hzbound hx, hzbound hy]
    have hab : |dist (g x).fst (g y).fst - dist (g x) (g y)| ≤ 2 * B := by
      rw [abs_sub_comm]
      exact hprod.trans hz'
    exact (abs_sub_le _ _ _).trans ((add_le_add hab hraw).trans_eq (by dsimp [ε]; ring))
  · intro y hy
    have hylarge : dist (WithLp.toLp 2 (y, z₀)) (WithLp.toLp 2 (0, z₀)) ≤ 2 - η := by
      rw [metric_prod_same_second]
      linarith
    obtain ⟨x, hx, hxy⟩ := hg.2.2 (WithLp.toLp 2 (y, z₀)) hylarge
    refine ⟨x, ?_, (WithLp.dist_fst_le _ _).trans (hxy.trans hε)⟩
    have hdist := (abs_le.mp (hg.2.1 x p hx hpp)).1
    have htri : dist (g x) (g p) ≤
        dist (g x) (WithLp.toLp 2 (y, z₀)) + dist y 0 +
        dist (WithLp.toLp 2 (0, z₀)) (g p) := by
      calc
        _ ≤ dist (g x) (WithLp.toLp 2 (y, z₀)) +
            dist (WithLp.toLp 2 (y, z₀)) (g p) := dist_triangle _ _ _
        _ ≤ _ := by
          have ht := dist_triangle (WithLp.toLp 2 (y, z₀)) (WithLp.toLp 2 (0, z₀)) (g p)
          rw [metric_prod_same_second] at ht
          linarith
    have hp := hg.1
    rw [dist_comm (g p)] at hp
    apply (div_le_iff₀ hr).mp
    linarith

end RegularPointCoordinates

end

end OAI
