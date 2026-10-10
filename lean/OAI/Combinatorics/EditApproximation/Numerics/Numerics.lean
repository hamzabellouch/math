import OAI.Combinatorics.EditApproximation.Geometry.Regret
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

/-- The conditional-gradient step size in the finite entropy optimizer. -/
noncomputable def frankWolfeStep (j : ℕ) : ℝ := 2 / ((j : ℝ) + 2)

theorem frankWolfeStep_nonnegative (j : ℕ) : 0 ≤ frankWolfeStep j := by
  unfold frankWolfeStep
  positivity

theorem frankWolfeStep_le_one (j : ℕ) : frankWolfeStep j ≤ 1 := by
  unfold frankWolfeStep
  apply (div_le_one₀ (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

/-- The scalar induction step giving the optimizer's `8/(σ(j+1))`
error term. -/
theorem frank_wolfe_scalar_step (σ error x : ℝ) (hσ : 0 < σ) (hx : 0 ≤ x) :
    (1 - 2 / (x + 3)) * (2 * error + 8 / (σ * (x + 2))) +
        2 * error * (2 / (x + 3)) + 2 * (2 / (x + 3)) ^ 2 / σ ≤
      2 * error + 8 / (σ * (x + 3)) := by
  have h2 : 0 < x + 2 := by linarith
  have h3 : 0 < x + 3 := by linarith
  have hid :
      (2 * error + 8 / (σ * (x + 3))) -
        ((1 - 2 / (x + 3)) * (2 * error + 8 / (σ * (x + 2))) +
          2 * error * (2 / (x + 3)) + 2 * (2 / (x + 3)) ^ 2 / σ) =
        8 / (σ * (x + 2) * (x + 3) ^ 2) := by
    field_simp [hσ.ne', h2.ne', h3.ne']
    ring
  have hnonneg : 0 ≤ 8 / (σ * (x + 2) * (x + 3) ^ 2) := by positivity
  linarith

/-- The first update removes dependence on the initial objective gap.
The conclusion corresponds to manuscript indices `j ≥ 1`. -/
theorem frank_wolfe_gap_bound (σ error : ℝ) (gap : ℕ → ℝ)
    (hσ : 0 < σ)
    (hrecurrence : ∀ j,
      gap (j + 1) ≤ (1 - frankWolfeStep j) * gap j +
        2 * error * frankWolfeStep j + 2 * (frankWolfeStep j) ^ 2 / σ) :
    ∀ j : ℕ, gap (j + 1) ≤ 2 * error + 8 / (σ * ((j : ℝ) + 2)) := by
  intro j
  induction j with
  | zero =>
    have hfirst : gap 1 ≤ 2 * error + 2 / σ := by
      simpa [frankWolfeStep] using hrecurrence 0
    have hratio : 8 / (σ * (0 + 2)) = 4 / σ := by ring
    rw [Nat.cast_zero, hratio]
    have hnonneg : 0 ≤ 2 / σ := by positivity
    have hratio' : 4 / σ = 2 * (2 / σ) := by ring
    rw [hratio']
    norm_num only [Nat.zero_add]
    linarith
  | succ j ih =>
    have hstep : frankWolfeStep (j + 1) = 2 / ((j : ℝ) + 3) := by
      norm_num [frankWolfeStep, Nat.cast_add, add_assoc]
    have hcoef : 0 ≤ 1 - frankWolfeStep (j + 1) :=
      sub_nonneg.mpr (frankWolfeStep_le_one _)
    have hmono := mul_le_mul_of_nonneg_left ih hcoef
    have hrec := hrecurrence (j + 1)
    rw [hstep] at hmono hrec
    have hscalar := frank_wolfe_scalar_step σ error (j : ℝ) hσ (Nat.cast_nonneg _)
    have hbound : gap (j + 1 + 1) ≤ 2 * error + 8 / (σ * ((j : ℝ) + 3)) := by
      linarith
    convert hbound using 1
    norm_num [Nat.cast_add, add_assoc]

/-- Exact rational weight of the vertex selected at step `j`, after
`K` steps. -/
def optimizerMixtureWeight (K j : ℕ) : ℚ :=
  2 * ((j : ℚ) + 1) / ((K : ℚ) * ((K : ℚ) + 1))

theorem sum_optimizer_numerators (K : ℕ) :
    (∑ j ∈ range K, 2 * ((j : ℚ) + 1)) = (K : ℚ) * ((K : ℚ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem optimizerMixtureWeight_positive (K j : ℕ) (hK : 0 < K) :
    0 < optimizerMixtureWeight K j := by
  unfold optimizerMixtureWeight
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  positivity

theorem sum_optimizerMixtureWeight (K : ℕ) (hK : 0 < K) :
    (∑ j ∈ range K, optimizerMixtureWeight K j) = 1 := by
  unfold optimizerMixtureWeight
  rw [← sum_div, sum_optimizer_numerators]
  apply div_self
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  positivity

theorem optimizerMixtureWeight_update_old (K j : ℕ) (hK : 0 < K) :
    (1 - 2 / ((K : ℚ) + 2)) * optimizerMixtureWeight K j =
      optimizerMixtureWeight (K + 1) j := by
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  ring

theorem optimizerMixtureWeight_update_new (K : ℕ) :
    2 / ((K : ℚ) + 2) = optimizerMixtureWeight (K + 1) K := by
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  ring

/-- Exact rational conditional-gradient iterates. -/
def rationalOptimizerIterate {ι : Type*} (initial : ι → ℚ) (selected : ℕ → ι → ℚ) :
    ℕ → ι → ℚ
  | 0 => initial
  | j + 1 => fun i =>
    (1 - 2 / ((j : ℚ) + 2)) * rationalOptimizerIterate initial selected j i +
      (2 / ((j : ℚ) + 2)) * selected j i

/-- After the first update, the initial vertex has weight zero. The
remaining iterates are exactly the explicit rational triangular mixture
used by the fair-bit sampler in Section 9. -/
theorem rationalOptimizerIterate_eq_mixture {ι : Type*}
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ) (K : ℕ) (i : ι) :
    rationalOptimizerIterate initial selected (K + 1) i =
      ∑ j ∈ range (K + 1), optimizerMixtureWeight (K + 1) j * selected j i := by
  induction K with
  | zero => norm_num [rationalOptimizerIterate, optimizerMixtureWeight]
  | succ K ih =>
    rw [rationalOptimizerIterate]
    dsimp only
    rw [ih, mul_sum]
    conv_rhs => rw [sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro j hj
      rw [← mul_assoc, optimizerMixtureWeight_update_old (K + 1) j (by omega)]
    · rw [optimizerMixtureWeight_update_new]

/-- Cumulative integer mass for the triangular exact sampler. -/


theorem optimizerTriangularMass_succ (K : ℕ) :
    optimizerTriangularMass (K + 1) = optimizerTriangularMass K + (K + 1) := by
  unfold optimizerTriangularMass
  rw [sum_range_succ]

theorem optimizerTriangularMass_twice (K : ℕ) :
    2 * optimizerTriangularMass K = K * (K + 1) := by
  induction K with
  | zero => simp [optimizerTriangularMass]
  | succ K ih =>
    rw [optimizerTriangularMass_succ]
    nlinarith

/-- The integers assigned to selection index `j` form a block of
exactly `j+1` points. -/
theorem optimizerSampler_block_card (j : ℕ) :
    (Icc (optimizerTriangularMass j + 1) (optimizerTriangularMass (j + 1))).card = j + 1 := by
  rw [Nat.card_Icc, optimizerTriangularMass_succ]
  omega

/-- Counting the fair uniform integer sampler gives exactly the stored
mixture weights, including repeated selected vertices. -/
theorem optimizerSampler_block_weight (K j : ℕ) (hK : 0 < K) :
    ((j + 1 : ℕ) : ℚ) / optimizerTriangularMass K = optimizerMixtureWeight K j := by
  have hK' : 0 < (K : ℚ) := Nat.cast_pos.mpr hK
  have hmass : 2 * (optimizerTriangularMass K : ℚ) = (K : ℚ) * ((K : ℚ) + 1) := by
    exact_mod_cast optimizerTriangularMass_twice K
  have hmasspos : 0 < (optimizerTriangularMass K : ℚ) := by nlinarith
  unfold optimizerMixtureWeight
  push_cast
  field_simp
  nlinarith

/-- The increase of `-x log x` after adding a positive smoothing
parameter is bounded by that parameter's own entropy. -/
theorem entropy_smoothing_upper (x σ : ℝ) (hx : 0 ≤ x) (hσ : 0 < σ) :
    Real.negMulLog (x + σ) - Real.negMulLog x ≤ Real.negMulLog σ := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hlogσ : 0 ≤ Real.log (x + σ) - Real.log σ :=
      sub_nonneg.mpr (Real.log_le_log hσ (by linarith))
    have hlogx : 0 ≤ Real.log (x + σ) - Real.log x :=
      sub_nonneg.mpr (Real.log_le_log hxpos (by linarith))
    have hprodσ := mul_nonneg hσ.le hlogσ
    have hprodx := mul_nonneg hx hlogx
    simp only [Real.negMulLog]
    nlinarith

/-- The negative change in the smoothed entropy coordinate is linear
in the smoothing parameter on the relevant interval `[0,2]`. -/
theorem entropy_smoothing_lower (x σ : ℝ) (hx : 0 ≤ x) (hσ : 0 < σ)
    (hupper : x + σ ≤ 2) :
    Real.negMulLog x - Real.negMulLog (x + σ) ≤ 2 * σ := by
  have hxs : 0 < x + σ := by linarith
  have hlog : Real.log (x + σ) ≤ 1 := by
    exact (Real.log_le_log hxs hupper).trans (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith)
  have hσlog := mul_le_mul_of_nonneg_left hlog hσ.le
  by_cases hxzero : x = 0
  · rw [hxzero, zero_add] at hσlog
    simp only [hxzero, Real.negMulLog, zero_add, neg_zero, zero_mul, zero_sub]
    nlinarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hratio := Real.log_le_sub_one_of_pos (div_pos hxs hxpos)
    rw [Real.log_div hxs.ne' hxpos.ne'] at hratio
    have hratio' := mul_le_mul_of_nonneg_left hratio hx
    have hcancel : x * ((x + σ) / x - 1) = σ := by
      field_simp
      ring
    rw [hcancel] at hratio'
    simp only [Real.negMulLog]
    nlinarith

theorem negMulLog_le_two_sqrt (σ : ℝ) (hσ : 0 < σ) :
    Real.negMulLog σ ≤ 2 * Real.sqrt σ := by
  have hroot : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hsq : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
  have hdiv : σ / Real.sqrt σ = Real.sqrt σ := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith
  have hmul : σ * (Real.sqrt σ)⁻¹ = Real.sqrt σ := by
    simpa only [div_eq_mul_inv] using hdiv
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hroot)
  rw [Real.log_inv, Real.log_sqrt hσ.le] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * σ by positivity)
  simp only [Real.negMulLog]
  nlinarith

/-- A uniform coordinate modulus for entropy smoothing, valid including
zero coordinates. -/
theorem entropy_smoothing_coordinate (x σ : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    |Real.negMulLog (x + σ) - Real.negMulLog x| ≤ 2 * Real.sqrt σ := by
  have hupper := (entropy_smoothing_upper x σ hx hσ).trans (negMulLog_le_two_sqrt σ hσ)
  have hlower := entropy_smoothing_lower x σ hx hσ (by linarith)
  have hσroot : σ ≤ Real.sqrt σ := by
    have hsq : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
    have hroot := Real.sqrt_nonneg σ
    have hσsq : σ ^ 2 ≤ σ := by nlinarith
    nlinarith
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- Manuscript Equation `eq:entropy-smoothing`, with a slightly stronger
constant from the coordinate estimate. The linear coefficient vector
cancels, so the bound is independent of its magnitude. -/
theorem finite_entropy_smoothing_bound {ι : Type*} (coordinates : Finset ι)
    (p objective : ι → ℝ) (σ η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    |((∑ i ∈ coordinates, Real.negMulLog (p i + σ)) +
        η * ∑ i ∈ coordinates, objective i * p i) -
      entropyValue coordinates η objective p| ≤ 4 * coordinates.card * Real.sqrt σ := by
  rw [entropyValue_eq]
  have hcancel :
      ((∑ i ∈ coordinates, Real.negMulLog (p i + σ)) +
        η * ∑ i ∈ coordinates, objective i * p i) -
        ((∑ i ∈ coordinates, Real.negMulLog (p i)) +
          η * ∑ i ∈ coordinates, objective i * p i) =
        ∑ i ∈ coordinates, (Real.negMulLog (p i + σ) - Real.negMulLog (p i)) := by
    rw [sum_sub_distrib]
    ring
  rw [hcancel]
  calc
    _ ≤ ∑ i ∈ coordinates, |Real.negMulLog (p i + σ) - Real.negMulLog (p i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ coordinates, 2 * Real.sqrt σ := sum_le_sum fun i hi =>
      entropy_smoothing_coordinate (p i) σ (hp i hi)
        ((single_le_sum hp hi).trans hpsum.le) hσ hσ1
    _ ≤ 4 * coordinates.card * Real.sqrt σ := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : 0 ≤ (coordinates.card : ℝ) := Nat.cast_nonneg _
      have hroot := Real.sqrt_nonneg σ
      nlinarith

private theorem entropy_quadratic_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => z * Real.log z - z ^ 2 / 2)
      (Real.log x + 1 - x) x := by
  convert! (Real.hasDerivAt_mul_log hx.ne').sub
    (((hasDerivAt_id x).pow 2).div_const 2) using 1
  simp only [id_eq]
  ring

/-- Negative entropy minus half the square is convex on the probability
coordinate interval. This is the exact curvature bound used for the
objective-gap estimate in the finite optimizer. -/
theorem entropy_quadratic_convex :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun z : ℝ => z * Real.log z - z ^ 2 / 2) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc (0 : ℝ) 1)
  · exact (Real.continuous_mul_log.sub (by fun_prop)).continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact (entropy_quadratic_hasDerivAt x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    simp only [interior_Icc, Set.mem_Ioo] at hx hy
    rw [(entropy_quadratic_hasDerivAt x hx.1).deriv,
      (entropy_quadratic_hasDerivAt y hy.1).deriv]
    have hratio := Real.one_sub_inv_le_log_of_pos (div_pos hy.1 hx.1)
    have hinv : (y / x)⁻¹ = x / y := by field_simp
    rw [hinv, Real.log_div hy.1.ne' hx.1.ne'] at hratio
    have hscaled := mul_le_mul_of_nonneg_left hratio hy.1.le
    have hcancel : y * (1 - x / y) = y - x := by field_simp [hy.1.ne']
    rw [hcancel] at hscaled
    have hlog : 0 ≤ Real.log y - Real.log x :=
      sub_nonneg.mpr (Real.log_le_log hx.1 hxy)
    have hcorrection := mul_nonneg (show 0 ≤ 1 - y by linarith) hlog
    nlinarith

/-- The entropy coordinate gap is at least half the squared coordinate
distance, including the competitor value zero by continuity. -/
theorem entropy_coordinate_strong_gap (x y : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    (x - y) ^ 2 / 2 ≤
      x * Real.log x - y * Real.log y - (Real.log y + 1) * (x - y) := by
  have hderiv := entropy_quadratic_hasDerivAt y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hslope := entropy_quadratic_convex.slope_le_of_hasDerivAt
      ⟨hx, hx1⟩ ⟨hy.le, hy1⟩ hxy hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hxy)).mp hslope
    nlinarith
  · simp
  · have hslope := entropy_quadratic_convex.le_slope_of_hasDerivAt
      ⟨hy.le, hy1⟩ ⟨hx, hx1⟩ hyx hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hyx)).mp hslope
    nlinarith

/-- Relative entropy dominates half the squared Euclidean distance on
the finite probability simplex. -/
theorem finite_relative_entropy_sq_gap {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    (∑ i ∈ coordinates, (q i - p i) ^ 2) / 2 ≤
      ∑ i ∈ coordinates, q i * Real.log (q i / p i) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      (q i - p i) ^ 2 / 2 ≤ q i * Real.log (q i / p i) - q i + p i := by
    have hstrong := entropy_coordinate_strong_gap (q i) (p i) (hq i hi)
      ((single_le_sum hq hi).trans hqsum.le) (hp i hi)
      ((single_le_sum (fun j hj => (hp j hj).le) hi).trans hpsum.le)
    by_cases hqzero : q i = 0
    · simp only [hqzero, zero_mul, sub_zero, zero_sub] at hstrong ⊢
      nlinarith
    · rw [Real.log_div hqzero (hp i hi).ne']
      nlinarith
  have hsum := sum_le_sum hcoord
  rw [← sum_div, sum_add_distrib, sum_sub_distrib, hqsum, hpsum] at hsum
  linarith

/-- A true entropy-objective gap controls the `ℓ₁` error of a feasible
mixture, with the manuscript's exact factor `sqrt (2d gap)`. -/
theorem entropy_gap_to_l1 {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective maximizer mixture : ι → ℝ)
    (hconvex : Convex ℝ Q) (hmaxQ : maximizer ∈ Q) (hmixQ : mixture ∈ Q)
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmix : ∀ i ∈ coordinates, 0 ≤ mixture i)
    (hmaxsum : ∑ i ∈ coordinates, maximizer i = 1)
    (hmixsum : ∑ i ∈ coordinates, mixture i = 1)
    (hmaximize : IsMaxOn (entropyValue coordinates η objective) Q maximizer) :
    (∑ i ∈ coordinates, |mixture i - maximizer i|) ≤
      Real.sqrt (2 * coordinates.card *
        (entropyValue coordinates η objective maximizer -
          entropyValue coordinates η objective mixture)) := by
  have hpenalty := entropy_hull_penalty coordinates Q η objective maximizer mixture
    hconvex hmaxQ hmixQ hmax hmaxsum hmixsum hmaximize
  have hsq := finite_relative_entropy_sq_gap coordinates maximizer mixture hmax hmix hmaxsum hmixsum
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul coordinates
    (fun _ _ => (show (0 : ℝ) ≤ 1 by norm_num))
    (fun i _ => sq_nonneg (mixture i - maximizer i))
    (fun i _ => (show |mixture i - maximizer i| ^ 2 ≤ 1 * (mixture i - maximizer i) ^ 2 by
      rw [one_mul, sq_abs]))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hcs
  apply Real.le_sqrt_of_sq_le
  have hc : 0 ≤ (coordinates.card : ℝ) := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left (show
      (∑ i ∈ coordinates, (mixture i - maximizer i) ^ 2) ≤
        2 * (entropyValue coordinates η objective maximizer -
          entropyValue coordinates η objective mixture) by linarith) hc
  nlinarith

/-- Converting a uniform smoothing error and a smoothed objective gap
to a gap for the true entropy objective. -/
theorem smoothing_gap_transfer (trueBest trueValue smoothBest smoothValue error gap : ℝ)
    (hbest : trueBest ≤ smoothBest + error)
    (hvalue : smoothValue ≤ trueValue + error)
    (hgap : smoothBest - smoothValue ≤ gap) :
    trueBest - trueValue ≤ gap + 2 * error := by linarith

theorem optimizer_work_budget_gap (G : ℝ) (hG : 0 < G) :
    8 / ((1 / G ^ 50) * (G ^ 80 + 1)) ≤ 8 / G ^ 30 := by
  have hpow : G ^ 80 = G ^ 50 * G ^ 30 := by rw [← pow_add]
  have hcancel : (1 / G ^ 50) * G ^ 80 = G ^ 30 := by
    rw [hpow]
    field_simp
  have hdenom : G ^ 30 ≤ (1 / G ^ 50) * (G ^ 80 + 1) := by
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hG _) hdenom

theorem optimizer_smoothing_root (G : ℝ) (hG : 0 < G) :
    Real.sqrt (1 / G ^ 50) = 1 / G ^ 25 := by
  have hpow : G ^ 50 = (G ^ 25) ^ 2 := by rw [← pow_mul]
  rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_one, Real.sqrt_sq_eq_abs,
    abs_of_pos (pow_pos hG _)]

/-- The explicit total objective-gap bound after the prescribed
number of fixed-step updates. -/
theorem optimizer_explicit_gap_budget (G d : ℝ) (hG : 4 ≤ G) (hd : d ≤ G) :
    2 / G ^ 20 + 8 / G ^ 30 + 8 * d / G ^ 25 ≤ 12 / G ^ 20 := by
  have hGpos : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hG10 : 4 ≤ G ^ 10 := hG.trans (by
    simpa using pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 10))
  have hG5 : d ≤ G ^ 5 := hd.trans (by
    simpa using pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 5))
  have hsmall : 8 / G ^ 30 ≤ 2 / G ^ 20 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_left hG10 (show 0 ≤ 2 * G ^ 20 by positivity)
    have hpow : G ^ 30 = G ^ 20 * G ^ 10 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hsmooth : 8 * d / G ^ 25 ≤ 8 / G ^ 20 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_left hG5 (show 0 ≤ 8 * G ^ 20 by positivity)
    have hpow : G ^ 25 = G ^ 20 * G ^ 5 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hsum : 2 / G ^ 20 + 2 / G ^ 20 + 8 / G ^ 20 = 12 / G ^ 20 := by ring
  linarith

/-- The quantitative final `H^(-3)` precision calculation. The squared
distance premise is supplied by the proved entropy/KL curvature bound. -/
theorem optimizer_final_l1_precision (H G d distance gap : ℝ)
    (hH : 4 ≤ H) (hHG : H ≤ G) (hd : 0 ≤ d) (hdG : d ≤ G)
    (hsquared : distance ^ 2 ≤ 2 * d * gap) (hgap : gap ≤ 12 / G ^ 20) :
    distance ≤ 1 / H ^ 3 := by
  have hHpos : 0 < H := by linarith
  have hGpos : 0 < G := lt_of_lt_of_le hHpos hHG
  have hG4 : 4 ≤ G := hH.trans hHG
  have hG1 : 1 ≤ G := by linarith
  have hG3 : 64 ≤ G ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hG4 3
    norm_num at h
    exact h
  have hG13 : 24 ≤ G ^ 13 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 3 ≤ 13)
    linarith
  have hratio : 24 / G ^ 19 ≤ 1 / G ^ 6 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_right hG13 (pow_nonneg hGpos.le 6)
    have hpow : G ^ 19 = G ^ 13 * G ^ 6 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hHratio : 1 / G ^ 6 ≤ 1 / H ^ 6 :=
    div_le_div_of_nonneg_left zero_le_one (pow_pos hHpos _)
      (pow_le_pow_left₀ hHpos.le hHG 6)
  have hscale := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * d by positivity)
  have hdimension := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdG (by norm_num : (0 : ℝ) ≤ 24))
    (pow_nonneg hGpos.le 20)
  have hcancel : 24 * G / G ^ 20 = 24 / G ^ 19 := by
    have hpow : G ^ 20 = G ^ 19 * G := by rw [← pow_succ]
    rw [hpow]
    field_simp
  have hsquare : distance ^ 2 ≤ 1 / H ^ 6 := by
    rw [hcancel] at hdimension
    have hcombined := hdimension.trans (hratio.trans hHratio)
    have hscaledGap : 2 * d * (12 / G ^ 20) = 24 * d / G ^ 20 := by ring
    rw [hscaledGap] at hscale
    exact hsquared.trans (hscale.trans hcombined)
  have htarget : (1 / H ^ 3) ^ 2 = 1 / H ^ 6 := by
    rw [div_pow, one_pow, ← pow_mul]
  have hpositive : 0 < 1 / H ^ 3 := by positivity
  rw [← htarget] at hsquare
  nlinarith

/-- Rational truncated logarithm used for the entropy-gradient
calculation. Its evaluation uses only rational arithmetic. -/


theorem rationalLogApproximation_cast (r : ℚ) (K : ℕ) :
    (rationalLogApproximation r K : ℝ) =
      2 * ∑ k ∈ range K,
        ((((r : ℝ) - 1) / ((r : ℝ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) := by
  unfold rationalLogApproximation
  push_cast
  rfl

theorem logarithm_symmetric_parameter_bound (r σ : ℝ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ r) (hrupper : r ≤ 1 + σ) :
    |(r - 1) / (r + 1)| ≤ 1 - σ := by
  have hrpos : 0 < r := hσ.trans_le hr
  have hrden : 0 < r + 1 := by linarith
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hrden).mpr
    have hprod := mul_nonneg hrpos.le (show 0 ≤ 1 - σ by linarith)
    nlinarith
  · apply (div_le_iff₀ hrden).mpr
    have hmul := mul_le_mul_of_nonneg_left hrupper hσ.le
    have hσsquare : σ ^ 2 ≤ σ / 2 := by
      have h := mul_le_mul_of_nonneg_left hσhalf hσ.le
      nlinarith
    nlinarith

/-- Explicit logarithm-series remainder for the rational gradient
routine. Mathlib's logarithm remainder is specialized to the bounded
smoothed-coordinate interval. Its bound suffices for the prescribed
polynomial truncation length. -/
theorem logarithm_series_error (r σ : ℝ) (K : ℕ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ r) (hrupper : r ≤ 1 + σ) :
    |Real.log r - 2 * ∑ k ∈ range K,
        (((r - 1) / (r + 1)) ^ (2 * k + 1) / (2 * k + 1))| ≤
      2 * Real.exp (-2 * K * σ) / σ := by
  let b := (r - 1) / (r + 1)
  have hrpos : 0 < r := hσ.trans_le hr
  have hrden : 0 < r + 1 := by linarith
  have hb : |b| ≤ 1 - σ := logarithm_symmetric_parameter_bound r σ hσ hσhalf hr hrupper
  have hb1 : |b| < 1 := by linarith
  have htransform : (1 + b) / (1 - b) = r := by
    dsimp only [b]
    field_simp
    ring
  have hseries := Real.sum_range_sub_log_div_le hb1 K
  rw [htransform] at hseries
  have htwice := mul_le_mul_of_nonneg_left hseries (show (0 : ℝ) ≤ 2 by norm_num)
  have hleft :
      |Real.log r - 2 * ∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1)| =
        2 * |1 / 2 * Real.log r - ∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1)| := by
    rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), ← abs_mul]
    congr 1
    ring
  rw [← hleft, ← mul_div_assoc] at htwice
  have hdenom : σ ≤ 1 - b ^ 2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs] at hsq
    have hσsq : σ ^ 2 ≤ σ := by nlinarith
    nlinarith
  have hnum : |b| ^ (2 * K + 1) ≤ Real.exp (-2 * K * σ) := by
    calc
      _ ≤ (1 - σ) ^ (2 * K + 1) := pow_le_pow_left₀ (abs_nonneg b) hb _
      _ ≤ Real.exp (-σ) ^ (2 * K + 1) := pow_le_pow_left₀
        (show 0 ≤ 1 - σ by linarith) (Real.one_sub_le_exp_neg σ) _
      _ = Real.exp ((2 * K + 1 : ℕ) * (-σ)) := (Real.exp_nat_mul (-σ) _).symm
      _ ≤ Real.exp (-2 * K * σ) := Real.exp_le_exp.mpr (by push_cast; nlinarith)
  calc
    _ ≤ 2 * |b| ^ (2 * K + 1) / (1 - b ^ 2) := htwice
    _ ≤ 2 * Real.exp (-2 * K * σ) / (1 - b ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num))
        (hσ.le.trans hdenom)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hσ hdenom

theorem rationalLogApproximation_error (r : ℚ) (σ : ℝ) (K : ℕ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ (r : ℝ)) (hrupper : (r : ℝ) ≤ 1 + σ) :
    |Real.log (r : ℝ) - (rationalLogApproximation r K : ℝ)| ≤
      2 * Real.exp (-2 * K * σ) / σ := by
  rw [rationalLogApproximation_cast]
  exact logarithm_series_error (r : ℝ) σ K hσ hσhalf hr hrupper

theorem logarithm_truncation_exponential_budget (G : ℝ) (hG : 4 ≤ G) :
    2 * Real.exp (-2 * G ^ 10) / (1 / G ^ 50) ≤ 1 / G ^ 20 := by
  have hGpos : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hG5 : 1024 ≤ G ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hG 5
    norm_num at h
    exact h
  have hG10 : 315 ≤ G ^ 10 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 5 ≤ 10)
    linarith
  have hpoly : 2 * G ^ 70 ≤ (2 * G ^ 10) ^ 8 / (8 : ℕ).factorial := by
    norm_num
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 40320)).mpr
    rw [mul_pow, ← pow_mul]
    have hpow : G ^ 80 = G ^ 70 * G ^ 10 := by rw [← pow_add]
    norm_num
    rw [hpow]
    have hscale := mul_le_mul_of_nonneg_left hG10 (show 0 ≤ 256 * G ^ 70 by positivity)
    nlinarith
  have hexp : 2 * G ^ 70 ≤ Real.exp (2 * G ^ 10) :=
    hpoly.trans (Real.pow_div_factorial_le_exp (x := 2 * G ^ 10) (n := 8) (by positivity))
  have heq : 2 * Real.exp (-2 * G ^ 10) / (1 / G ^ 50) =
      2 * G ^ 50 / Real.exp (2 * G ^ 10) := by
    rw [show -2 * G ^ 10 = -(2 * G ^ 10) by ring, Real.exp_neg]
    field_simp [hGpos.ne']
  rw [heq]
  apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hGpos _)).mpr
  have hpow : G ^ 50 * G ^ 20 = G ^ 70 := by rw [← pow_add]
  nlinarith

/-- The prescribed rational logarithm computation has the required
absolute gradient precision `G^(-20)` after `G^60` rational terms. -/
theorem rationalLogApproximation_prescribed_precision (r : ℚ) (G : ℕ)
    (hG : 4 ≤ G)
    (hr : 1 / (G : ℝ) ^ 50 ≤ (r : ℝ))
    (hrupper : (r : ℝ) ≤ 1 + 1 / (G : ℝ) ^ 50) :
    |Real.log (r : ℝ) - (rationalLogApproximation r (G ^ 60) : ℝ)| ≤
      1 / (G : ℝ) ^ 20 := by
  have hG4 : (4 : ℝ) ≤ G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := by linarith
  have hG1 : (1 : ℝ) ≤ G := by linarith
  have hG50 : (2 : ℝ) ≤ (G : ℝ) ^ 50 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 50)
    norm_num only [pow_one] at hmono
    linarith
  have hσpos : 0 < 1 / (G : ℝ) ^ 50 := by positivity
  have hσhalf : 1 / (G : ℝ) ^ 50 ≤ 1 / 2 := by
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hG50
  have herror := rationalLogApproximation_error r (1 / (G : ℝ) ^ 50) (G ^ 60)
    hσpos hσhalf hr hrupper
  have hprod : ((G ^ 60 : ℕ) : ℝ) * (1 / (G : ℝ) ^ 50) = (G : ℝ) ^ 10 := by
    push_cast
    have hpow : (G : ℝ) ^ 60 = (G : ℝ) ^ 10 * (G : ℝ) ^ 50 := by rw [← pow_add]
    rw [hpow]
    field_simp
  have hexponent : -2 * ((G ^ 60 : ℕ) : ℝ) * (1 / (G : ℝ) ^ 50) =
      -2 * (G : ℝ) ^ 10 := by nlinarith [hprod]
  rw [hexponent] at herror
  exact herror.trans (logarithm_truncation_exponential_budget (G : ℝ) hG4)

theorem finite_gradient_error {ι : Type*} (coordinates : Finset ι)
    (gradient approximateGradient p : ι → ℝ) (error : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (herror : ∀ i ∈ coordinates, |approximateGradient i - gradient i| ≤ error) :
    |∑ i ∈ coordinates, (approximateGradient i - gradient i) * p i| ≤ error := by
  calc
    _ ≤ ∑ i ∈ coordinates, |(approximateGradient i - gradient i) * p i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ coordinates, error * p i := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hp i hi)]
      exact mul_le_mul_of_nonneg_right (herror i hi) (hp i hi)
    _ = error := by rw [← mul_sum, hpsum, mul_one]

/-- Enumerating the vertices with an approximate gradient loses at
most `2e₀` in the true linearization, even against an arbitrary feasible
mixture. -/
theorem approximate_gradient_linearization_loss {ι : Type*} (coordinates : Finset ι)
    (gradient approximateGradient selected competitor : ι → ℝ) (error : ℝ)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hcompetitor : ∀ i ∈ coordinates, 0 ≤ competitor i)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hcompetitorSum : ∑ i ∈ coordinates, competitor i = 1)
    (herror : ∀ i ∈ coordinates, |approximateGradient i - gradient i| ≤ error)
    (hchoose : (∑ i ∈ coordinates, approximateGradient i * competitor i) ≤
      ∑ i ∈ coordinates, approximateGradient i * selected i) :
    (∑ i ∈ coordinates, gradient i * competitor i) -
        (∑ i ∈ coordinates, gradient i * selected i) ≤ 2 * error := by
  have hsel := finite_gradient_error coordinates gradient approximateGradient selected
    error hselected hselectedSum herror
  have hcomp := finite_gradient_error coordinates gradient approximateGradient competitor
    error hcompetitor hcompetitorSum herror
  simp only [sub_mul, sum_sub_distrib] at hsel hcomp
  have hselBounds := abs_le.mp hsel
  have hcompBounds := abs_le.mp hcomp
  linarith

noncomputable def smoothedEntropyValue {ι : Type*} (coordinates : Finset ι)
    (σ : ℝ) (linear p : ι → ℝ) : ℝ :=
  ∑ i ∈ coordinates, (Real.negMulLog (p i + σ) + linear i * p i)

noncomputable def smoothedEntropyGradient {ι : Type*}
    (σ : ℝ) (linear p : ι → ℝ) (i : ι) : ℝ :=
  -Real.log (p i + σ) - 1 + linear i

/-- Tangent upper bound for a single smoothed entropy coordinate. -/
theorem smoothed_entropy_coordinate_upper (x y σ linear : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 < σ) :
    (Real.negMulLog (y + σ) + linear * y) -
        (Real.negMulLog (x + σ) + linear * x) ≤
      (-Real.log (x + σ) - 1 + linear) * (y - x) := by
  have hxs : 0 < x + σ := by linarith
  have hys : 0 < y + σ := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxs hys)
  rw [Real.log_div hxs.ne' hys.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hys.le
  have hcancel : (y + σ) * ((x + σ) / (y + σ) - 1) = x - y := by
    field_simp
    ring
  rw [hcancel] at hscaled
  simp only [Real.negMulLog]
  nlinarith

/-- A scalar smoothness bound obtained directly from `log u ≤ u-1`.
The coefficient `1/σ` combines with the sharper simplex diameter below
to give the manuscript's exact `2 ξ²/σ` remainder. -/
theorem smoothed_entropy_coordinate_lower (x y σ linear : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 < σ) :
    (-Real.log (x + σ) - 1 + linear) * (y - x) - (y - x) ^ 2 / σ ≤
      (Real.negMulLog (y + σ) + linear * y) -
        (Real.negMulLog (x + σ) + linear * x) := by
  have hxs : 0 < x + σ := by linarith
  have hys : 0 < y + σ := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hys hxs)
  rw [Real.log_div hys.ne' hxs.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hys.le
  have hcancel : (y + σ) * ((y + σ) / (x + σ) - 1) - y + x =
      (y - x) ^ 2 / (x + σ) := by
    field_simp
    ring
  have hratio : (y - x) ^ 2 / (x + σ) ≤ (y - x) ^ 2 / σ :=
    div_le_div_of_nonneg_left (sq_nonneg _) hσ (by linarith)
  have hbound : (y + σ) * (Real.log (y + σ) - Real.log (x + σ)) - y + x ≤
      (y - x) ^ 2 / (x + σ) := by linarith
  have hbound' := hbound.trans hratio
  simp only [Real.negMulLog]
  nlinarith

theorem probability_vectors_sq_distance_le_two {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    ∑ i ∈ coordinates, (q i - p i) ^ 2 ≤ 2 := by
  have hcoord (i : ι) (hi : i ∈ coordinates) : (q i - p i) ^ 2 ≤ q i + p i := by
    have hp1 := (single_le_sum hp hi).trans hpsum.le
    have hq1 := (single_le_sum hq hi).trans hqsum.le
    have hpprod := mul_nonneg (hp i hi) (sub_nonneg.mpr hp1)
    have hqprod := mul_nonneg (hq i hi) (sub_nonneg.mpr hq1)
    have hpq := mul_nonneg (hp i hi) (hq i hi)
    nlinarith
  calc
    _ ≤ ∑ i ∈ coordinates, (q i + p i) := sum_le_sum hcoord
    _ = 2 := by rw [sum_add_distrib, hqsum, hpsum]; norm_num

theorem smoothed_entropy_tangent_upper {ι : Type*} (coordinates : Finset ι)
    (σ : ℝ) (linear p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i) (hσ : 0 < σ) :
    smoothedEntropyValue coordinates σ linear q - smoothedEntropyValue coordinates σ linear p ≤
      ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (q i - p i) := by
  rw [smoothedEntropyValue, smoothedEntropyValue, ← sum_sub_distrib]
  exact sum_le_sum fun i hi => smoothed_entropy_coordinate_upper (p i) (q i) σ
    (linear i) (hp i hi) (hq i hi) hσ

theorem smoothed_entropy_mixture_lower {ι : Type*} (coordinates : Finset ι)
    (σ ξ : ℝ) (linear p selected : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hσ : 0 < σ) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    ξ * (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (selected i - p i)) -
        2 * ξ ^ 2 / σ ≤
      smoothedEntropyValue coordinates σ linear
          (fun i => (1 - ξ) * p i + ξ * selected i) - smoothedEntropyValue coordinates σ linear p := by
  let updated : ι → ℝ := fun i => (1 - ξ) * p i + ξ * selected i
  have hupdated (i : ι) (hi : i ∈ coordinates) : 0 ≤ updated i :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hξ1) (hp i hi))
      (mul_nonneg hξ (hselected i hi))
  have hcoordinate (i : ι) (hi : i ∈ coordinates) :=
    smoothed_entropy_coordinate_lower (p i) (updated i) σ (linear i) (hp i hi) (hupdated i hi) hσ
  have hsum := sum_le_sum hcoordinate
  have hterm (i : ι) : updated i - p i = ξ * (selected i - p i) := by
    dsimp only [updated]
    ring
  simp only [smoothedEntropyGradient] at hsum ⊢
  simp_rw [hterm, mul_pow, div_eq_mul_inv] at hsum
  rw [sum_sub_distrib] at hsum
  have hlinear :
      (∑ i ∈ coordinates, (-Real.log (p i + σ) - 1 + linear i) * (ξ * (selected i - p i))) =
        ξ * ∑ i ∈ coordinates, (-Real.log (p i + σ) - 1 + linear i) * (selected i - p i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have hquadratic : (∑ i ∈ coordinates, ξ ^ 2 * (selected i - p i) ^ 2 * σ⁻¹) =
      (ξ ^ 2 / σ) * ∑ i ∈ coordinates, (selected i - p i) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hlinear, hquadratic, sum_sub_distrib] at hsum
  have hdiameter := probability_vectors_sq_distance_le_two coordinates p selected hp hselected hpsum hselectedSum
  have hscale := mul_le_mul_of_nonneg_left hdiameter (show 0 ≤ ξ ^ 2 / σ by positivity)
  change _ ≤ smoothedEntropyValue coordinates σ linear updated -
    smoothedEntropyValue coordinates σ linear p at hsum
  change _ ≤ smoothedEntropyValue coordinates σ linear updated -
    smoothedEntropyValue coordinates σ linear p
  have htwo : ξ ^ 2 / σ * 2 = 2 * ξ ^ 2 / σ := by ring
  rw [htwo] at hscale
  linarith

/-- The manuscript's fixed-step optimizer recurrence follows from the
actual smoothed entropy objective and approximate gradient selection. -/
theorem smoothed_frank_wolfe_recurrence {ι : Type*} (coordinates : Finset ι)
    (σ ξ error : ℝ) (linear p selected best approximateGradient : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hbestSum : ∑ i ∈ coordinates, best i = 1)
    (hσ : 0 < σ) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hgradient : ∀ i ∈ coordinates,
      |approximateGradient i - smoothedEntropyGradient σ linear p i| ≤ error)
    (hchoose : (∑ i ∈ coordinates, approximateGradient i * best i) ≤
      ∑ i ∈ coordinates, approximateGradient i * selected i) :
    smoothedEntropyValue coordinates σ linear best -
        smoothedEntropyValue coordinates σ linear (fun i => (1 - ξ) * p i + ξ * selected i) ≤
      (1 - ξ) * (smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear p) +
        2 * error * ξ + 2 * ξ ^ 2 / σ := by
  have htangent := smoothed_entropy_tangent_upper coordinates σ linear p best hp hbest hσ
  have hlinear := approximate_gradient_linearization_loss coordinates
    (smoothedEntropyGradient σ linear p) approximateGradient selected best error
    hselected hbest hselectedSum hbestSum hgradient hchoose
  have hlower := smoothed_entropy_mixture_lower coordinates σ ξ linear p selected
    hp hselected hpsum hselectedSum hσ hξ hξ1
  have hsumBest : (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (best i - p i)) =
      (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * best i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by
    simp only [mul_sub, sum_sub_distrib]
  have hsumSelected : (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (selected i - p i)) =
      (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * selected i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by
    simp only [mul_sub, sum_sub_distrib]
  rw [hsumBest] at htangent
  rw [hsumSelected] at hlower
  have hgain : smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear p -
      2 * error ≤ (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * selected i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by linarith
  have hscale := mul_le_mul_of_nonneg_left hgain hξ
  nlinarith

/-- Casting the exact rational update gives precisely the analytic step. -/
theorem rationalOptimizerIterate_cast_step {ι : Type*}
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ) (j : ℕ) :
    (fun i => (rationalOptimizerIterate initial selected (j + 1) i : ℝ)) =
      (fun i => (1 - frankWolfeStep j) * (rationalOptimizerIterate initial selected j i : ℝ) +
        frankWolfeStep j * (selected j i : ℝ)) := by
  funext i
  simp [rationalOptimizerIterate, frankWolfeStep]

/-- All exact rational iterates are probability vectors. -/
theorem rationalOptimizerIterate_probability {ι : Type*} (coordinates : Finset ι)
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1) :
    ∀ j, (∀ i ∈ coordinates, (0 : ℝ) ≤ rationalOptimizerIterate initial selected j i) ∧
      (∑ i ∈ coordinates, (rationalOptimizerIterate initial selected j i : ℝ)) = 1 := by
  intro j
  induction j with
  | zero => exact ⟨hinitial, hinitialSum⟩
  | succ j ih =>
    have hstep := congr_fun (rationalOptimizerIterate_cast_step initial selected j)
    constructor
    · intro i hi
      rw [hstep i]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr (frankWolfeStep_le_one j)) (ih.1 i hi))
        (mul_nonneg (frankWolfeStep_nonnegative j) (hselected j i hi))
    · simp_rw [hstep]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ih.2, hselectedSum]
      ring

/-- Convex feasibility is preserved by the actual rational iterates. -/
theorem rationalOptimizerIterate_mem {ι : Type*}
    (Q : Set (ι → ℝ)) (initial : ι → ℚ) (selected : ℕ → ι → ℚ)
    (hconvex : Convex ℝ Q) (hinitial : (fun i => (initial i : ℝ)) ∈ Q)
    (hselected : ∀ j, (fun i => (selected j i : ℝ)) ∈ Q) :
    ∀ j, (fun i => (rationalOptimizerIterate initial selected j i : ℝ)) ∈ Q := by
  intro j
  induction j with
  | zero => exact hinitial
  | succ j ih =>
    rw [rationalOptimizerIterate_cast_step]
    exact hconvex ih (hselected j) (sub_nonneg.mpr (frankWolfeStep_le_one j))
      (frankWolfeStep_nonnegative j) (by ring)

/-- Objective convergence of the exact rational implementation follows
from the proved smoothness and rational approximate-gradient choices. -/
theorem rational_optimizer_smoothed_gap_bound {ι : Type*} (coordinates : Finset ι)
    (σ error : ℝ) (linear best : ι → ℝ) (initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (approximateGradient : ℕ → ι → ℝ)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hbestSum : ∑ i ∈ coordinates, best i = 1) (hσ : 0 < σ)
    (hgradient : ∀ j i, i ∈ coordinates →
      |approximateGradient j i - smoothedEntropyGradient σ linear
        (fun i => (rationalOptimizerIterate initial selected j i : ℝ)) i| ≤ error)
    (hchoose : ∀ j, (∑ i ∈ coordinates, approximateGradient j i * best i) ≤
      ∑ i ∈ coordinates, approximateGradient j i * (selected j i : ℝ)) :
    ∀ j, smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear
      (fun i => (rationalOptimizerIterate initial selected (j + 1) i : ℝ)) ≤
        2 * error + 8 / (σ * ((j : ℝ) + 2)) := by
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum
  apply frank_wolfe_gap_bound σ error
    (fun j => smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear
      (fun i => (rationalOptimizerIterate initial selected j i : ℝ))) hσ
  intro j
  rw [rationalOptimizerIterate_cast_step]
  exact smoothed_frank_wolfe_recurrence coordinates σ (frankWolfeStep j) error linear
    (fun i => (rationalOptimizerIterate initial selected j i : ℝ))
    (fun i => (selected j i : ℝ)) best (approximateGradient j)
    (hprobability j).1 (hselected j) hbest (hprobability j).2 (hselectedSum j) hbestSum hσ
    (frankWolfeStep_nonnegative j) (frankWolfeStep_le_one j) (hgradient j) (hchoose j)

/-- The actual rational gradient routine, including exact linear terms. -/


theorem rationalSmoothedGradient_precision {ι : Type*} (coordinates : Finset ι)
    (G : ℕ) (linear p : ι → ℚ) (hG : 4 ≤ G)
    (hp : ∀ i ∈ coordinates, (0 : ℝ) ≤ p i)
    (hpsum : ∑ i ∈ coordinates, (p i : ℝ) = 1) :
    ∀ i ∈ coordinates,
      |(rationalSmoothedGradient G linear p i : ℝ) -
        smoothedEntropyGradient (1 / (G : ℝ) ^ 50)
          (fun i => (linear i : ℝ)) (fun i => (p i : ℝ)) i| ≤ 1 / (G : ℝ) ^ 20 := by
  intro i hi
  have hinput : (1 / (G : ℝ) ^ 50) ≤ (p i + 1 / (G : ℚ) ^ 50 : ℚ) := by
    push_cast
    linarith [hp i hi]
  have hupper : ((p i + 1 / (G : ℚ) ^ 50 : ℚ) : ℝ) ≤ 1 + 1 / (G : ℝ) ^ 50 := by
    push_cast
    linarith [(single_le_sum hp hi).trans hpsum.le]
  have hlog := rationalLogApproximation_prescribed_precision
    (p i + 1 / (G : ℚ) ^ 50) G hG hinput hupper
  convert hlog using 1
  congr 1
  simp only [rationalSmoothedGradient, smoothedEntropyGradient]
  push_cast
  ring

/-- The prescribed number of exact rational updates reaches the true
entropy-objective precision, with no assumed analytic recurrence. -/
theorem rational_optimizer_true_gap_precision {ι : Type*} (coordinates : Finset ι)
    (G : ℕ) (linear initial : ι → ℚ) (selected : ℕ → ι → ℚ) (best : ι → ℝ)
    (hG : 4 ≤ G) (hdG : coordinates.card ≤ G)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hbestSum : ∑ i ∈ coordinates, best i = 1)
    (hchoose : ∀ j,
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * best i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * (selected j i : ℝ)) :
    entropyValue coordinates 1 (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
          12 / (G : ℝ) ^ 20 := by
  let σ : ℝ := 1 / (G : ℝ) ^ 50
  have hG4 : (4 : ℝ) ≤ G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := by linarith
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    apply (div_le_one₀ (pow_pos hGpos _)).mpr
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ G)
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum
  have hgradient j := rationalSmoothedGradient_precision coordinates G linear
    (rationalOptimizerIterate initial selected j) hG (hprobability j).1 (hprobability j).2
  have hgap := rational_optimizer_smoothed_gap_bound coordinates σ (1 / (G : ℝ) ^ 20)
    (fun i => (linear i : ℝ)) best initial selected
    (fun j i => (rationalSmoothedGradient G linear (rationalOptimizerIterate initial selected j) i : ℝ))
    hinitial hinitialSum hselected hselectedSum hbest hbestSum hσ hgradient hchoose (G ^ 80 - 1)
  have hK : 1 ≤ G ^ 80 := by
    have hGnat : 0 < G := by omega
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 80 (Nat.ne_of_gt hGnat))
  rw [Nat.sub_add_cancel hK] at hgap
  have hindex : ((G ^ 80 - 1 : ℕ) : ℝ) + 2 = (G : ℝ) ^ 80 + 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one, Nat.cast_pow]
    ring
  rw [hindex] at hgap
  have hbudget := optimizer_work_budget_gap (G : ℝ) hGpos
  have hsmoothed : smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ)) best -
      smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
          2 / (G : ℝ) ^ 20 + 8 / (G : ℝ) ^ 30 := by
    dsimp only [σ] at hgap ⊢
    have htwo : (2 : ℝ) * (1 / (G : ℝ) ^ 20) = 2 / (G : ℝ) ^ 20 := by ring
    rw [htwo] at hgap
    linarith
  have hbestSmoothing := finite_entropy_smoothing_bound coordinates best
    (fun i => (linear i : ℝ)) σ 1 hbest hbestSum hσ hσ1
  have hvalueSmoothing := finite_entropy_smoothing_bound coordinates
    (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))
    (fun i => (linear i : ℝ)) σ 1 (hprobability _).1 (hprobability _).2 hσ hσ1
  have hbestSmooth : |smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ)) best| ≤
      4 * coordinates.card * Real.sqrt σ := by
    simpa [smoothedEntropyValue, sum_add_distrib] using hbestSmoothing
  have hvalueSmooth : |smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ))
      (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) -
        entropyValue coordinates 1 (fun i => (linear i : ℝ))
          (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))| ≤
      4 * coordinates.card * Real.sqrt σ := by
    simpa [smoothedEntropyValue, sum_add_distrib] using hvalueSmoothing
  have htrue : entropyValue coordinates 1 (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
      2 / (G : ℝ) ^ 20 + 8 / (G : ℝ) ^ 30 + 8 * coordinates.card * Real.sqrt σ := by
    have hb := abs_le.mp hbestSmooth
    have hv := abs_le.mp hvalueSmooth
    linarith
  have hroot : Real.sqrt σ = 1 / (G : ℝ) ^ 25 := optimizer_smoothing_root _ hGpos
  rw [hroot] at htrue
  have hdimension : (coordinates.card : ℝ) ≤ G := by exact_mod_cast hdG
  have hfinal := optimizer_explicit_gap_budget (G : ℝ) coordinates.card hG4 hdimension
  have hnorm : (8 : ℝ) * coordinates.card * (1 / (G : ℝ) ^ 25) =
      8 * coordinates.card / (G : ℝ) ^ 25 := by ring
  rw [hnorm] at htrue
  exact htrue.trans hfinal

/-- The final distance guarantee for the prescribed rational updates.
Only their concrete finite linearization choices remain as input. -/
theorem rational_optimizer_l1_precision {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (H G : ℕ) (linear initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (maximizer : ι → ℝ)
    (hH : 4 ≤ H) (hHG : H ≤ G) (hdG : coordinates.card ≤ G)
    (hconvex : Convex ℝ Q) (hinitialQ : (fun i => (initial i : ℝ)) ∈ Q)
    (hselectedQ : ∀ j, (fun i => (selected j i : ℝ)) ∈ Q)
    (hmaxQ : maximizer ∈ Q)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmaxSum : ∑ i ∈ coordinates, maximizer i = 1)
    (hmaximize : IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ))) Q maximizer)
    (hchoose : ∀ j,
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * maximizer i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * (selected j i : ℝ)) :
    (∑ i ∈ coordinates,
      |(rationalOptimizerIterate initial selected (G ^ 80) i : ℝ) - maximizer i|) ≤
        1 / (H : ℝ) ^ 3 := by
  have hG : 4 ≤ G := hH.trans hHG
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum (G ^ 80)
  have hmixture := rationalOptimizerIterate_mem Q initial selected
    hconvex hinitialQ hselectedQ (G ^ 80)
  have hgap := rational_optimizer_true_gap_precision coordinates G linear initial selected maximizer
    hG hdG hinitial hinitialSum hselected hselectedSum (fun i hi => (hmax i hi).le) hmaxSum hchoose
  have hdistance := entropy_gap_to_l1 coordinates Q 1 (fun i => (linear i : ℝ)) maximizer
    (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) hconvex
    hmaxQ hmixture hmax hprobability.1 hmaxSum hprobability.2 hmaximize
  have hmaxbound := hmaximize hmixture
  change entropyValue coordinates 1 (fun i => (linear i : ℝ))
      (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
    entropyValue coordinates 1 (fun i => (linear i : ℝ)) maximizer at hmaxbound
  have hnonnegative : 0 ≤ 2 * (coordinates.card : ℝ) *
      (entropyValue coordinates 1 (fun i => (linear i : ℝ)) maximizer -
        entropyValue coordinates 1 (fun i => (linear i : ℝ))
          (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))) := by positivity
  have hsquared := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hdistance 2
  rw [Real.sq_sqrt hnonnegative] at hsquared
  apply optimizer_final_l1_precision (H : ℝ) G coordinates.card _ _
    (by exact_mod_cast hH) (by exact_mod_cast hHG) (Nat.cast_nonneg _)
    (by exact_mod_cast hdG) hsquared hgap

/-- Maximizing a finite list's linearization also maximizes it on the
real convex hull. -/
theorem finite_linearization_maximizes_convexHull {ι : Type*} (coordinates : Finset ι)
    (vertices : Set (ι → ℝ)) (gradient selected : ι → ℝ)
    (hchoose : ∀ p ∈ vertices,
      (∑ i ∈ coordinates, gradient i * p i) ≤ ∑ i ∈ coordinates, gradient i * selected i) :
    ∀ p ∈ convexHull ℝ vertices,
      (∑ i ∈ coordinates, gradient i * p i) ≤ ∑ i ∈ coordinates, gradient i * selected i := by
  let bound := ∑ i ∈ coordinates, gradient i * selected i
  have hconvex : Convex ℝ {p : ι → ℝ | (∑ i ∈ coordinates, gradient i * p i) ≤ bound} := by
    intro p hp q hq a b ha hb hab
    change (∑ i ∈ coordinates, gradient i * (a * p i + b * q i)) ≤ bound
    have hlinear : (∑ i ∈ coordinates, gradient i * (a * p i + b * q i)) =
        a * (∑ i ∈ coordinates, gradient i * p i) +
        b * (∑ i ∈ coordinates, gradient i * q i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hlinear]
    have hp' := mul_le_mul_of_nonneg_left hp ha
    have hq' := mul_le_mul_of_nonneg_left hq hb
    have hbound : a * bound + b * bound = bound := by rw [← add_mul, hab, one_mul]
    linarith
  exact convexHull_min hchoose hconvex

/-- Executable finite rational comparisons, with the first listed
maximizer selected in a tie. The fallback only applies to an empty list. -/


theorem rationalLinearizationMaximizer_spec {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) (hvertices : vertices ≠ []) :
    rationalLinearizationMaximizer coordinates vertices gradient ∈ vertices ∧
      ∀ p ∈ vertices, (∑ i ∈ coordinates, gradient i * p i) ≤
        ∑ i ∈ coordinates, gradient i * rationalLinearizationMaximizer coordinates vertices gradient i := by
  unfold rationalLinearizationMaximizer
  cases harg : vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp harg))
  | some selected =>
    simp only [Option.getD_some]
    have hmem : selected ∈ vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) := by
      rw [harg]
      simp
    exact ⟨List.argmax_mem hmem, fun p hp => List.le_of_mem_argmax
      (f := fun p : ι → ℚ => ∑ i ∈ coordinates, gradient i * p i) hp hmem⟩

/-- The finite rational optimizer: every operation here is rational
arithmetic, finite enumeration, or the prescribed finite logarithm sum. -/


def finiteOptimizerSelection {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) : ι → ℚ :=
  rationalLinearizationMaximizer coordinates vertices
    (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))

theorem finiteRationalOptimizer_eq_iterate {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer coordinates vertices linear G j =
      rationalOptimizerIterate (vertices.headD (fun _ => 0))
        (finiteOptimizerSelection coordinates vertices linear G) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext i
    simp only [finiteRationalOptimizer, rationalOptimizerIterate]
    change (1 - 2 / ((j : ℚ) + 2)) * finiteRationalOptimizer coordinates vertices linear G j i +
        2 / ((j : ℚ) + 2) * finiteOptimizerSelection coordinates vertices linear G j i = _
    rw [ih]

def rationalVertexSet {ι : Type*} (vertices : List (ι → ℚ)) : Set (ι → ℝ) :=
  (fun p : ι → ℚ => fun i => (p i : ℝ)) '' {p | p ∈ vertices}

/-- Every vector in the listed real convex hull is a probability vector. -/
theorem rationalVertexHull_probability {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ))
    (hvertices : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1) :
    ∀ p ∈ convexHull ℝ (rationalVertexSet vertices),
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i) = 1 := by
  have hconvex : Convex ℝ {p : ι → ℝ |
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i) = 1} := by
    intro p hp q hq a b ha hb hab
    constructor
    · intro i hi
      exact add_nonneg (mul_nonneg ha (hp.1 i hi)) (mul_nonneg hb (hq.1 i hi))
    · change (∑ i ∈ coordinates, (a * p i + b * q i)) = 1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp.2, hq.2, mul_one, mul_one]
      exact hab
  apply convexHull_min _ hconvex
  rintro _ ⟨p, hp, rfl⟩
  exact hvertices p hp

/-- Concrete finite vertex selection satisfies the required
linearization inequality against every real feasible mixture. -/
theorem finiteOptimizerSelection_maximizes {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ)
    (hvertices : vertices ≠ []) :
    ∀ best ∈ convexHull ℝ (rationalVertexSet vertices),
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates vertices linear G j) i : ℝ) * best i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates vertices linear G j) i : ℝ) *
        (finiteOptimizerSelection coordinates vertices linear G j i : ℝ) := by
  apply finite_linearization_maximizes_convexHull
  rintro _ ⟨p, hp, rfl⟩
  have hspec := (rationalLinearizationMaximizer_spec coordinates vertices
    (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
    hvertices).2 p hp
  dsimp only [finiteOptimizerSelection]
  exact_mod_cast hspec

/-- Accuracy of the executable rational optimizer at every positive
entropy maximizer of its listed action hull. -/
theorem finiteRationalOptimizer_l1_precision {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (H : ℕ) (maximizer : ι → ℝ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hmaxQ : maximizer ∈ convexHull ℝ (rationalVertexSet vertices))
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmaximize : IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ)))
      (convexHull ℝ (rationalVertexSet vertices)) maximizer) :
    (∑ i ∈ coordinates, |(finiteRationalOptimizer coordinates vertices linear
      (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80) i : ℝ) - maximizer i|) ≤
        1 / (H : ℝ) ^ 3 := by
  let G := H + coordinates.card + 2
  let initial : ι → ℚ := vertices.headD (fun _ => 0)
  let selected := finiteOptimizerSelection coordinates vertices linear G
  have hinitialMem : initial ∈ vertices := by
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons p tail => exact List.mem_cons_self
  have hselectedMem j : selected j ∈ vertices :=
    (rationalLinearizationMaximizer_spec coordinates vertices
      (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
      hvertices).1
  have hinitialQ : (fun i => (initial i : ℝ)) ∈ convexHull ℝ (rationalVertexSet vertices) :=
    subset_convexHull ℝ _ ⟨initial, hinitialMem, rfl⟩
  have hselectedQ j : (fun i => (selected j i : ℝ)) ∈ convexHull ℝ (rationalVertexSet vertices) :=
    subset_convexHull ℝ _ ⟨selected j, hselectedMem j, rfl⟩
  have hmaxProbability := rationalVertexHull_probability coordinates vertices hprobability maximizer hmaxQ
  have hchoose j := finiteOptimizerSelection_maximizes coordinates vertices linear G j
    hvertices maximizer hmaxQ
  simp_rw [finiteRationalOptimizer_eq_iterate] at hchoose ⊢
  exact rational_optimizer_l1_precision coordinates (convexHull ℝ (rationalVertexSet vertices)) H G
    linear initial selected maximizer hH (by dsimp [G]; omega) (by dsimp [G]; omega)
    (convex_convexHull ℝ _) hinitialQ hselectedQ hmaxQ
    (hprobability initial hinitialMem).1 (hprobability initial hinitialMem).2
    (fun j => (hprobability (selected j) (hselectedMem j)).1)
    (fun j => (hprobability (selected j) (hselectedMem j)).2)
    hmax hmaxProbability.2 hmaximize hchoose

/-- Averaging the finite action list gives a feasible vector positive
at every covered coordinate, including lists with repeated actions. -/
theorem rationalVertexHull_positive_witness {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (hvertices : vertices ≠ [])
    (hnonnegative : ∀ p ∈ vertices, ∀ i ∈ coordinates, (0 : ℝ) ≤ p i)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i) :
    ∃ witness ∈ convexHull ℝ (rationalVertexSet vertices),
      ∀ i ∈ coordinates, 0 < witness i := by
  classical
  let listed := vertices.toFinset
  have hlisted : listed.Nonempty := (List.toFinset_nonempty_iff vertices).mpr hvertices
  have hcard : 0 < (listed.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hlisted)
  let weight : ℝ := 1 / listed.card
  have hweight : 0 < weight := by dsimp [weight]; positivity
  have hweightSum : (∑ _ ∈ listed, weight) = 1 := by
    simp only [sum_const, nsmul_eq_mul]
    dsimp only [weight]
    field_simp
  let witness : ι → ℝ := ∑ p ∈ listed, weight • (fun i => (p i : ℝ))
  refine ⟨witness, ?_, ?_⟩
  · exact (convex_convexHull ℝ (rationalVertexSet vertices)).sum_mem
      (fun _ _ => hweight.le) hweightSum (fun p hp =>
        subset_convexHull ℝ _ ⟨p, List.mem_toFinset.mp hp, rfl⟩)
  · intro i hi
    dsimp only [witness]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨p, hp, hpi⟩ := hcovered i hi
    exact sum_pos' (fun q hq => mul_nonneg hweight.le
      (hnonnegative q (List.mem_toFinset.mp hq) i hi))
      ⟨p, List.mem_toFinset.mpr hp, mul_pos hweight hpi⟩

/-- The finite optimizer accuracy theorem with exactly the manuscript's
probability and coordinate-coverage assumptions. The returned point is
the executable rational construction defined above. -/
theorem finite_entropy_optimizer {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (H : ℕ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i) :
    ∃ maximizer ∈ convexHull ℝ (rationalVertexSet vertices),
      IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ)))
        (convexHull ℝ (rationalVertexSet vertices)) maximizer ∧
      (∑ i ∈ coordinates, |(finiteRationalOptimizer coordinates vertices linear
        (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80) i : ℝ) - maximizer i|) ≤
          1 / (H : ℝ) ^ 3 := by
  classical
  have hfinite : ({p : ι → ℚ | p ∈ vertices} : Set (ι → ℚ)).Finite := by
    simp
  have hcompact := (hfinite.image (fun p : ι → ℚ => fun i => (p i : ℝ))).isCompact_convexHull ℝ
  obtain ⟨witness, hwitnessQ, hwitness⟩ := rationalVertexHull_positive_witness coordinates vertices
    hvertices (fun p hp => (hprobability p hp).1) hcovered
  obtain ⟨maximizer, hmaxQ, hmaximize⟩ := exists_entropy_maximizer coordinates
    (convexHull ℝ (rationalVertexSet vertices)) 1 (fun i => (linear i : ℝ)) hcompact ⟨witness, hwitnessQ⟩
  have hmaxProbability := rationalVertexHull_probability coordinates vertices hprobability maximizer hmaxQ
  have hmax := entropy_hull_maximizer_positive coordinates (convexHull ℝ (rationalVertexSet vertices))
    1 (fun i => (linear i : ℝ)) maximizer witness (convex_convexHull ℝ _) hmaxQ hwitnessQ
    hmaxProbability.1 hwitness hmaximize
  exact ⟨maximizer, hmaxQ, hmaximize, finiteRationalOptimizer_l1_precision coordinates vertices linear H
    maximizer hvertices hH hprobability hmaxQ hmax hmaximize⟩

end EditApproximation

end OAI
