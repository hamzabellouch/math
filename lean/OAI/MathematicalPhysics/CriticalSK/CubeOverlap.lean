import OAI.MathematicalPhysics.CriticalSK.SphereGeometry

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter
open scoped Topology
open MeasureTheory Filter Set Real
namespace CriticalSK

def latticeOverlap (n j : ℕ) : ℝ := -1 + 2 * j / n

def cubeOverlapMass (n j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n * n.choose j

lemma cubeOverlapMass_nonneg (n j : ℕ) : 0 ≤ cubeOverlapMass n j := by
  unfold cubeOverlapMass; positivity

lemma latticeOverlap_mul {n j : ℕ} (hn : 0 < n) :
    n * latticeOverlap n j = 2 * (j : ℝ) - n := by
  unfold latticeOverlap
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma binomial_exp_term {n j : ℕ} (hj : j ≤ n) (t : ℝ) :
    Real.exp (t * (2 * (j : ℝ) - n)) = Real.exp t ^ j * Real.exp (-t) ^ (n-j) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub hj]
  congr 1
  ring

lemma cubeOverlapMass_exp_bound {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) (t : ℝ) :
    cubeOverlapMass n j * Real.exp (t * n * latticeOverlap n j) ≤ Real.cosh t ^ n := by
  have hs : Real.exp t ^ j * Real.exp (-t) ^ (n-j) * (n.choose j : ℝ) ≤
      (Real.exp t + Real.exp (-t)) ^ n := by
    rw [add_pow]
    exact Finset.single_le_sum (f := fun i => Real.exp t ^ i * Real.exp (-t) ^ (n-i) * (n.choose i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (show j < n+1 by omega))
  have ht : t * n * latticeOverlap n j = t * (2 * (j : ℝ) - n) := by
    rw [mul_assoc, latticeOverlap_mul hn]
  rw [cubeOverlapMass, ht, binomial_exp_term hj t, Real.cosh_eq, div_pow]
  calc
    (2 : ℝ)⁻¹ ^ n * (n.choose j : ℝ) * (Real.exp t ^ j * Real.exp (-t) ^ (n-j)) =
        (Real.exp t ^ j * Real.exp (-t) ^ (n-j) * (n.choose j : ℝ)) / 2 ^ n := by
          rw [inv_pow]; ring
    _ ≤ (Real.exp t + Real.exp (-t)) ^ n / 2 ^ n := div_le_div_of_nonneg_right hs (by positivity)

lemma cubeOverlapMass_chernoff {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    cubeOverlapMass n j ≤ Real.exp (-(n : ℝ) * latticeOverlap n j ^ 2 / 2) := by
  set q := latticeOverlap n j
  have h := cubeOverlapMass_exp_bound hn hj q
  have hc : Real.cosh q ^ n ≤ Real.exp ((n : ℝ) * q ^ 2 / 2) := by
    calc
      Real.cosh q ^ n ≤ Real.exp (q ^ 2 / 2) ^ n :=
        pow_le_pow_left₀ (Real.cosh_pos q).le (Real.cosh_le_exp_half_sq q) n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmul : Real.exp (-(n : ℝ) * q ^ 2 / 2) * Real.exp (q * n * q) =
      Real.exp ((n : ℝ) * q ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (q * n * q))).mp
  rw [hmul]
  exact h.trans hc

def binaryEntropyRate (q : ℝ) : ℝ :=
  ((1+q)*Real.log (1+q)+(1-q)*Real.log (1-q))/2

lemma log_cubic_error {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (1-q) + q + q^2/2 + q^3/3| ≤ 2*q^4 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |q| < 1 by linarith) 3
  have half : (0:ℝ) < 1-|q| := by linarith
  have hr : |q|^4/(1-|q|) ≤ 2*q^4 := by
    rw [div_le_iff₀ half, pow_abs, abs_of_nonneg (show 0 ≤ q^4 by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ 1/2-|q| by linarith) (show 0 ≤ q^4 by positivity)]
  calc
    |Real.log (1-q)+q+q^2/2+q^3/3| =
      |(∑ i ∈ range 3, q^(i+1)/(i+1)) + Real.log (1-q)| := by
        congr 1
        norm_num [sum_range_succ]
        ring
    _ ≤ _ := h
    _ ≤ _ := hr

lemma binaryEntropyRate_taylor {q : ℝ} (hq : |q| ≤ 1/2) :
    |binaryEntropyRate q-q^2/2| ≤ 4*q^4 := by
  have hqp := abs_le.mp hq
  let Ep := Real.log (1+q)-q+q^2/2-q^3/3
  let Em := Real.log (1-q)+q+q^2/2+q^3/3
  have hp : |Ep| ≤ 2*q^4 := by
    have hp0 := log_cubic_error (q := -q) (by simpa using hq)
    have heq : Real.log (1-(-q))+(-q)+(-q)^2/2+(-q)^3/3 = Ep := by dsimp [Ep]; ring_nf
    rw [heq] at hp0
    convert hp0 using 1; ring
  have hm : |Em| ≤ 2*q^4 := log_cubic_error hq
  have h1p : |1+q| ≤ 3/2 := by rw [abs_le]; constructor <;> linarith
  have h1m : |1-q| ≤ 3/2 := by rw [abs_le]; constructor <;> linarith
  have hid : binaryEntropyRate q-q^2/2 = ((1+q)*Ep+(1-q)*Em)/2 + q^4/3 := by
    unfold binaryEntropyRate Ep Em
    ring
  rw [hid]
  calc
    |((1+q)*Ep+(1-q)*Em)/2 + q^4/3| ≤
        (|1+q| *|Ep|+|1-q| *|Em|)/2 + q^4/3 := by
      calc
        _ ≤ |((1+q)*Ep+(1-q)*Em)/2| + |q^4/3| := abs_add_le _ _
        _ = |(1+q)*Ep+(1-q)*Em|/2 + q^4/3 := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (show 0 ≤ q^4/3 by positivity)]
        _ ≤ _ := by gcongr; simpa only [abs_mul] using abs_add_le ((1+q)*Ep) ((1-q)*Em)
    _ ≤ ((3/2)*(2*q^4)+(3/2)*(2*q^4))/2 + q^4/3 := by gcongr
    _ ≤ 4*q^4 := by nlinarith [show 0 ≤ q^4 by positivity]

lemma log_square_error {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (1-q^2)+q^2| ≤ 2*q^4 := by
  have hq2 : q^2 ≤ 1/4 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have h := Real.abs_log_sub_add_sum_range_le (x := q^2) (by rw [abs_of_nonneg (sq_nonneg q)]; linarith) 1
  norm_num [abs_of_nonneg (sq_nonneg q)] at h
  rw [add_comm] at h
  calc
    _ ≤ (q^2)^2/(1-q^2) := h
    _ ≤ 2*q^4 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1-q^2)]
      nlinarith [mul_nonneg (show 0 ≤ 1/2-q^2 by linarith) (show 0 ≤ q^4 by positivity)]

lemma entropy_error_tendsto {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*q n^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)*(binaryEntropyRate (q n)-q n^2/2)) atTop (𝓝 0) := by
  have hev : ∀ᶠ n in atTop, |q n| ≤ 1/2 :=
    (hq.abs).eventually (eventually_le_nhds (by norm_num : |(0:ℝ)| < 1/2))
  apply squeeze_zero_norm' _ (by simpa using hfour.const_mul 4)
  filter_upwards [hev] with n hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    (n:ℝ)*|binaryEntropyRate (q n)-q n^2/2| ≤ (n:ℝ)*(4*q n^4) :=
      mul_le_mul_of_nonneg_left (binaryEntropyRate_taylor hn) (Nat.cast_nonneg n)
    _ = 4*((n:ℝ)*q n^4) := by ring

def stirlingLogError (n : ℕ) : ℝ := Real.log (Stirling.stirlingSeq n) - Real.log Real.pi/2

lemma stirlingLogError_tendsto : Tendsto stirlingLogError atTop (𝓝 0) := by
  change Tendsto (fun n => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi/2) atTop (𝓝 0)
  have h := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have hh := h.sub_const (Real.log Real.pi/2)
  simpa only [Function.comp_apply, Real.log_sqrt Real.pi_pos.le, sub_self] using hh

lemma log_factorial_stirling_exact {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = (n:ℝ)*Real.log n-n+Real.log n/2+
      Real.log (2*Real.pi)/2+stirlingLogError n := by
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  unfold stirlingLogError
  linarith

lemma latticeOverlap_interior {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    -1 < latticeOverlap n j ∧ latticeOverlap n j < 1 := by
  have hn : (0:ℝ) < n := by exact_mod_cast (lt_trans hj hjn)
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have hjr : (j:ℝ) < n := by exact_mod_cast hjn
  unfold latticeOverlap
  constructor
  · have := div_pos (mul_pos (by norm_num : (0:ℝ) < 2) hj0) hn; linarith
  · have := (div_lt_iff₀ hn).mpr (show 2*(j:ℝ) < 2*n by linarith); linarith

lemma latticeOverlap_halves {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (j:ℝ) = n*(1+latticeOverlap n j)/2 ∧
    ((n-j:ℕ):ℝ) = n*(1-latticeOverlap n j)/2 := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  unfold latticeOverlap
  rw [Nat.cast_sub hj]
  constructor <;> field_simp <;> ring

lemma log_cubeOverlapMass_exact {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    Real.log (cubeOverlapMass n j) + Real.log n/2 +
      n*binaryEntropyRate (latticeOverlap n j) + Real.log (1-latticeOverlap n j^2)/2 =
    Real.log 2-Real.log (2*Real.pi)/2 +
      stirlingLogError n-stirlingLogError j-stirlingLogError (n-j) := by
  have hn : 0 < n := lt_trans hj hjn
  have hnj : 0 < n-j := Nat.sub_pos_of_lt hjn
  have hjp : (0:ℝ) < j := by exact_mod_cast hj
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hnjp : (0:ℝ) < (n-j:ℕ) := by exact_mod_cast hnj
  obtain ⟨hqm,hqp⟩ := latticeOverlap_interior hj hjn
  obtain ⟨hjhalf,hkhalf⟩ := latticeOverlap_halves hn hjn.le
  have hlj : Real.log (j:ℝ) = Real.log n+Real.log (1+latticeOverlap n j)-Real.log 2 := by
    conv_lhs => rw [hjhalf]
    rw [Real.log_div (mul_ne_zero hnp.ne' (by linarith)) (by norm_num), Real.log_mul hnp.ne' (by linarith)]
  have hlk : Real.log ((n-j:ℕ):ℝ) = Real.log n+Real.log (1-latticeOverlap n j)-Real.log 2 := by
    conv_lhs => rw [hkhalf]
    rw [Real.log_div (mul_ne_zero hnp.ne' (by linarith)) (by norm_num), Real.log_mul hnp.ne' (by linarith)]
  have hlq : Real.log (1-latticeOverlap n j^2) =
      Real.log (1+latticeOverlap n j)+Real.log (1-latticeOverlap n j) := by
    rw [show 1-latticeOverlap n j^2 = (1+latticeOverlap n j)*(1-latticeOverlap n j) by ring,
      Real.log_mul (by linarith) (by linarith)]
  rw [cubeOverlapMass, Real.log_mul (by positivity) (by exact_mod_cast (Nat.choose_pos hjn.le).ne'),
    Real.log_pow, Real.log_inv, Nat.cast_choose ℝ hjn.le,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    log_factorial_stirling_exact hn, log_factorial_stirling_exact hj, log_factorial_stirling_exact hnj,
    hlj, hlk, hlq]
  unfold binaryEntropyRate
  rw [hjhalf, hkhalf]
  ring

lemma cubeOverlapMass_pos {n j : ℕ} (hj : j ≤ n) : 0 < cubeOverlapMass n j := by
  unfold cubeOverlapMass
  exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos hj)

lemma cubeOverlapMass_local_limit {j : ℕ → ℕ}
    (hj : ∀ᶠ n : ℕ in atTop, j n ≤ n)
    (hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => cubeOverlapMass n (j n) * Real.sqrt n *
      Real.exp ((n:ℝ)*latticeOverlap n (j n)^2/2)) atTop
      (𝓝 (Real.exp (Real.log 2-Real.log (2*Real.pi)/2))) := by
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hqevent : ∀ᶠ n in atTop, |latticeOverlap n (j n)| < 1/2 :=
    hq.abs.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1/2))
  have hhalves : ∀ᶠ n : ℕ in atTop, (n:ℝ)/4 ≤ j n ∧ (n:ℝ)/4 ≤ (n-j n:ℕ) := by
    filter_upwards [hnpos,hj,hqevent] with n hn hjn hqn
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    obtain ⟨ha,hb⟩ := latticeOverlap_halves hn hjn
    have hab := abs_lt.mp hqn
    constructor <;> nlinarith
  have hjtop : Tendsto j atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    exact tendsto_atTop_mono' atTop (hhalves.mono fun n h => h.1)
      (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<4) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hktop : Tendsto (fun n => n-j n) atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    exact tendsto_atTop_mono' atTop (hhalves.mono fun n h => h.2)
      (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<4) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hint : ∀ᶠ n : ℕ in atTop, 0 < j n ∧ j n < n := by
    filter_upwards [hjtop.eventually_gt_atTop 0,hktop.eventually_gt_atTop 0] with n hn hk
    exact ⟨hn, Nat.sub_pos_iff_lt.mp hk⟩
  have hlq : Tendsto (fun n => Real.log (1-latticeOverlap n (j n)^2)/2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => 1-latticeOverlap n (j n)^2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (hq.pow 2)
    simpa using ((Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp ht).div_const 2
  have herr := ((stirlingLogError_tendsto.sub (stirlingLogError_tendsto.comp hjtop)).sub
    (stirlingLogError_tendsto.comp hktop)).sub (entropy_error_tendsto hq hfour)
  have hlim := (herr.const_add (Real.log 2-Real.log (2*Real.pi)/2)).sub hlq
  have hlog : Tendsto (fun n : ℕ => Real.log (cubeOverlapMass n (j n) * Real.sqrt n *
      Real.exp ((n:ℝ)*latticeOverlap n (j n)^2/2))) atTop
      (𝓝 (Real.log 2-Real.log (2*Real.pi)/2)) := by
    apply (show Tendsto (fun n : ℕ => Real.log 2-Real.log (2*Real.pi)/2 +
      ((stirlingLogError n-stirlingLogError (j n)-stirlingLogError (n-j n))-
        (n:ℝ)*(binaryEntropyRate (latticeOverlap n (j n))-latticeOverlap n (j n)^2/2))-
      Real.log (1-latticeOverlap n (j n)^2)/2) atTop _ from by simpa using hlim).congr'
    filter_upwards [hint,hnpos] with n hn hnp
    rw [Real.log_mul (mul_ne_zero (cubeOverlapMass_pos hn.2.le).ne' (by positivity)) (Real.exp_ne_zero _),
      Real.log_mul (cubeOverlapMass_pos hn.2.le).ne' (by positivity), Real.log_sqrt (by positivity), Real.log_exp]
    have h := log_cubeOverlapMass_exact hn.1 hn.2
    linarith
  apply (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr'
  filter_upwards [hj,hnpos] with n hjn hn
  dsimp only [Function.comp_apply]
  exact Real.exp_log (mul_pos (mul_pos (cubeOverlapMass_pos hjn) (by positivity)) (Real.exp_pos _))

def scaledOverlapShape (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (1-x^2/(n+6)))^(n+3)

lemma sqrt_sub_le_exp (u : ℝ) : Real.sqrt (1-u) ≤ Real.exp (-u/2) := by
  rw [Real.sqrt_le_iff]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  calc
    1-u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    _ = Real.exp (-u/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma scaledOverlapShape_nonneg (n : ℕ) (x : ℝ) : 0 ≤ scaledOverlapShape n x := by
  unfold scaledOverlapShape; positivity

lemma scaledOverlapShape_bound (n : ℕ) (x : ℝ) :
    scaledOverlapShape n x ≤ Real.exp (-(1/4 : ℝ) * x^2) := by
  unfold scaledOverlapShape
  calc
    (Real.sqrt (1-x^2/(n+6)))^(n+3) ≤ Real.exp (-(x^2/(n+6))/2)^(n+3) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_sub_le_exp _) _
    _ = Real.exp (-((n+3 : ℕ) : ℝ) * x^2 / (2*(n+6))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hp : (0 : ℝ) < 2*((n : ℝ)+6) := by positivity
      rw [div_le_iff₀ hp]
      push_cast
      nlinarith [mul_nonneg hn (sq_nonneg x)]

lemma sqrt_nat_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a^n) = Real.sqrt a ^ n := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (pow_nonneg ha n), ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt ha]

lemma sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x/2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

lemma scaledOverlapShape_tendsto (x : ℝ) :
    Tendsto (fun n => scaledOverlapShape n x) atTop (𝓝 (Real.exp (-x^2/2))) := by
  have hinv : Tendsto (fun n : ℕ => (x^2 : ℝ)/(n+6)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 6 tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => (1 : ℝ)-x^2/(n+6)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hbpos : ∀ᶠ n : ℕ in atTop, 0 < (1 : ℝ)-x^2/(n+6) := hb.eventually (eventually_gt_nhds zero_lt_one)
  have hp := (Real.tendsto_one_add_div_pow_exp (-x^2)).comp (tendsto_add_atTop_nat 6)
  have hnum : Tendsto (fun n : ℕ => Real.sqrt ((1-x^2/(n+6))^(n+6))) atTop
      (𝓝 (Real.exp (-x^2/2))) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hp using 1
    · ext n; congr 2; push_cast; ring
    · rw [sqrt_exp_half]
  have hden : Tendsto (fun n : ℕ => Real.sqrt (1-x^2/(n+6))^3) atTop (𝓝 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hb).pow 3
  have hr := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hr
  apply hr.congr'
  filter_upwards [hbpos] with n hn
  dsimp only [Pi.div_apply]
  rw [sqrt_nat_pow hn.le]
  unfold scaledOverlapShape
  have hne : Real.sqrt (1-x^2/((n : ℝ)+6)) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  rw [show n+6 = n+3+3 by omega, pow_add]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 3 hne)

lemma scaledOverlapShape_integrable (n : ℕ) : Integrable (scaledOverlapShape n) := by
  apply (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).mono' (by unfold scaledOverlapShape; fun_prop)
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (scaledOverlapShape_nonneg n x)] using scaledOverlapShape_bound n x)

lemma scaledOverlapShape_integral_tendsto :
    Tendsto (fun n => ∫ x, scaledOverlapShape n x) atTop (𝓝 (Real.sqrt (2*Real.pi))) := by
  have h := @tendsto_integral_of_dominated_convergence ℝ ℝ _ _ _ volume
    scaledOverlapShape (fun x => Real.exp (-(1/2:ℝ)*x^2)) (fun x => Real.exp (-(1/4:ℝ)*x^2))
    (fun n => (scaledOverlapShape_integrable n).aestronglyMeasurable)
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4))
    (fun n => ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (scaledOverlapShape_nonneg n x)] using scaledOverlapShape_bound n x))
    (ae_of_all _ (fun x => by convert scaledOverlapShape_tendsto x using 1; congr 2; ring))
  convert h using 1
  rw [integral_gaussian]
  congr 2
  ring

lemma scaledOverlapShape_eq (n : ℕ) (x : ℝ) :
    scaledOverlapShape n x = sphereOverlapShape (n+6) (x/Real.sqrt (n+6)) := by
  simp only [scaledOverlapShape, sphereOverlapShape, show n+6-3 = n+3 by omega,
    div_pow]
  rw [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+6 by positivity)]

lemma overlapShape_normalizer_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt n * ∫ q : ℝ, sphereOverlapShape n q) atTop
      (𝓝 (Real.sqrt (2*Real.pi))) := by
  rw [← tendsto_add_atTop_iff_nat 6]
  convert scaledOverlapShape_integral_tendsto using 1
  ext n
  simp_rw [scaledOverlapShape_eq]
  rw [Measure.integral_comp_div, smul_eq_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  push_cast
  rfl

lemma sphereOverlapShape_pos {n : ℕ} {q : ℝ} (hq : |q| < 1) :
    0 < sphereOverlapShape n q := by
  unfold sphereOverlapShape
  apply pow_pos
  apply Real.sqrt_pos.mpr
  nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]

lemma sphereOverlapShape_log_error {n : ℕ} (hn : 3 ≤ n) {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2| ≤ (n:ℝ)*q^4+2*q^2 := by
  have hq2 : q^2 ≤ 1/4 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hnp : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnn : (0:ℝ) ≤ n-3 := by
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hid : Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2 =
      ((n:ℝ)-3)/2*(Real.log (1-q^2)+q^2)+3*q^2/2 := by
    rw [sphereOverlapShape, Real.log_pow, Real.log_sqrt (by linarith), Nat.cast_sub hn]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ |((n:ℝ)-3)/2| * |Real.log (1-q^2)+q^2| + 3*q^2/2 := by
      have h := abs_add_le (((n:ℝ)-3)/2*(Real.log (1-q^2)+q^2)) (3*q^2/2)
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 3*q^2/2 by positivity)] at h
      exact h
    _ = ((n:ℝ)-3)/2 * |Real.log (1-q^2)+q^2| + 3*q^2/2 := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ)-3)/2)]
    _ ≤ ((n:ℝ)-3)/2 * (2*q^4) + 3*q^2/2 := by gcongr; exact log_square_error hq
    _ ≤ _ := by nlinarith [show 0 ≤ q^4 by positivity, sq_nonneg q]

lemma sphereOverlapShape_local_limit {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*q n^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => sphereOverlapShape n (q n)*Real.exp ((n:ℝ)*q n^2/2))
      atTop (𝓝 1) := by
  have hev : ∀ᶠ n in atTop, |q n| ≤ 1/2 :=
    hq.abs.eventually (eventually_le_nhds (by norm_num : |(0:ℝ)| < 1/2))
  have hlog : Tendsto (fun n : ℕ => Real.log (sphereOverlapShape n (q n))+(n:ℝ)*q n^2/2)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n : ℕ => (n:ℝ)*q n^4+2*q n^2) atTop (𝓝 0) from by
      simpa using hfour.add ((hq.pow 2).const_mul 2))
    filter_upwards [hev,eventually_ge_atTop 3] with n hqn hn
    simpa only [Real.norm_eq_abs] using sphereOverlapShape_log_error hn hqn
  have he := Real.continuous_exp.continuousAt.tendsto.comp hlog
  rw [Real.exp_zero] at he
  apply he.congr'
  filter_upwards [hev] with n hn
  dsimp only [Function.comp_apply]
  rw [Real.exp_add, Real.exp_log (sphereOverlapShape_pos (lt_of_le_of_lt hn (by norm_num)))]

def sphereOverlapDensity (n : ℕ) (q : ℝ) : ℝ :=
  sphereOverlapShape n q / (∫ r : ℝ, sphereOverlapShape n r)

lemma local_overlap_constant : Real.exp (Real.log 2-Real.log (2*Real.pi)/2) *
    Real.sqrt (2*Real.pi) / 2 = 1 := by
  rw [Real.exp_sub, ← Real.log_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi),
    Real.exp_log (by norm_num : (0:ℝ)<2), Real.exp_log (by positivity)]
  field_simp

lemma local_overlap_const_pos : 0 < Real.sqrt (2*Real.pi) := by positivity

lemma cube_sphere_overlap_local_ratio {j : ℕ → ℕ}
    (hj : ∀ᶠ n : ℕ in atTop, j n ≤ n)
    (hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => cubeOverlapMass n (j n) /
      ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n (j n)))) atTop (𝓝 1) := by
  have hi := cubeOverlapMass_local_limit hj hq hfour
  have hs := sphereOverlapShape_local_limit hq hfour
  have hz := overlapShape_normalizer_tendsto
  have hr := (hi.mul hz).div (hs.const_mul 2) (by norm_num : (2:ℝ)*1≠0)
  simp only [mul_one, local_overlap_constant] at hr
  apply hr.congr'
  have heq : ∀ᶠ n in atTop, |latticeOverlap n (j n)| < 1 :=
    hq.abs.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1))
  have hzpos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt n * ∫ q : ℝ, sphereOverlapShape n q :=
    hz.eventually (eventually_gt_nhds local_overlap_const_pos)
  filter_upwards [eventually_gt_atTop 0,heq,hzpos] with n hn hq hnz
  dsimp only [Pi.div_apply, Pi.mul_apply]
  unfold sphereOverlapDensity
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hS : Real.sqrt n ≠ 0 := by positivity
  have hZ : (∫ q : ℝ, sphereOverlapShape n q) ≠ 0 :=
    (mul_ne_zero_iff.mp hnz.ne').2
  have hf := (sphereOverlapShape_pos (n:=n) hq).ne'
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma latticeOverlap_center_bound {n : ℕ} (hn : 0 < n) :
    |latticeOverlap n (n/2)| ≤ 1/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ha : 2*(n/2:ℕ) ≤ n := by omega
  have hb : n ≤ 2*(n/2:ℕ)+1 := by omega
  have haR : 2*((n/2:ℕ):ℝ) ≤ n := by exact_mod_cast ha
  have hbR : (n:ℝ) ≤ 2*((n/2:ℕ):ℝ)+1 := by exact_mod_cast hb
  rw [abs_le]
  unfold latticeOverlap
  constructor
  · have h := div_le_div_of_nonneg_right (show (-1:ℝ) ≤ 2*((n/2:ℕ):ℝ)-n by linarith) hnR.le
    calc
      -(1/(n:ℝ)) = (-1)/(n:ℝ) := by ring
      _ ≤ _ := h
      _ = -1+2*((n/2:ℕ):ℝ)/(n:ℝ) := by rw [sub_div,div_self hnR.ne']; ring
  · have : 2*((n/2:ℕ):ℝ)/(n:ℝ) ≤ 1 := (div_le_iff₀ hnR).mpr (by linarith)
    have : 0 ≤ 1/(n:ℝ) := by positivity
    linarith

lemma cube_sphere_overlap_uniform {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, |latticeOverlap n j| ≤ c n →
      |cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))-1| < ε := by
  intro ε hε
  let P (n j : ℕ) : Prop := j ≤ n ∧ |latticeOverlap n j| ≤ c n ∧
    ε ≤ |cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))-1|
  classical
  let j : ℕ → ℕ := fun n => if h : ∃ j, P n j then h.choose else n/2
  have hj : ∀ n, j n ≤ n := by
    intro n
    unfold j
    split_ifs with h
    · exact h.choose_spec.1
    · exact Nat.div_le_self _ _
  have hjc : ∀ᶠ n : ℕ in atTop, |latticeOverlap n (j n)| ≤ c n := by
    filter_upwards [hcmin,eventually_gt_atTop 0] with n hcn hn
    unfold j
    split_ifs with h
    · exact h.choose_spec.2.1
    · exact (latticeOverlap_center_bound hn).trans hcn
  have hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hc
    simpa only [Real.norm_eq_abs] using hjc
  have hq4 : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hc4
    filter_upwards [hjc] with n hn
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_abs, abs_of_nonneg (show 0 ≤ latticeOverlap n (j n)^4 by positivity)] using pow_le_pow_left₀ (abs_nonneg _) hn 4) (Nat.cast_nonneg n)
  have hr := cube_sphere_overlap_local_ratio (Eventually.of_forall hj) hq hq4
  have he : ∀ᶠ n : ℕ in atTop,
      |cubeOverlapMass n (j n) / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n (j n)))-1| < ε := by
    have h := (hr.sub_const 1).abs
    simpa only [sub_self,abs_zero] using h.eventually (eventually_lt_nhds (by simpa using hε))
  filter_upwards [he] with n hn
  intro k hkn hkc
  by_contra hbad
  have hex : ∃ k, P n k := ⟨k,hkn,hkc,not_lt.mp hbad⟩
  have : P n (j n) := by simpa only [j,dite_eq_left hex] using hex.choose_spec
  exact (not_le_of_gt hn) this.2.2

lemma sphereOverlapShape_continuous (n : ℕ) : Continuous (sphereOverlapShape n) := by
  unfold sphereOverlapShape
  fun_prop

lemma sphereOverlapShape_nonneg (n : ℕ) (q : ℝ) : 0 ≤ sphereOverlapShape n q := by
  unfold sphereOverlapShape
  positivity

lemma sphereOverlapShape_eq_zero {n : ℕ} (hn : 4 ≤ n) {q : ℝ} (hq : 1 ≤ |q|) :
    sphereOverlapShape n q = 0 := by
  unfold sphereOverlapShape
  rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_abs q]), zero_pow (by omega : n-3≠0)]

lemma sphereOverlapShape_integrable {n : ℕ} (hn : 4 ≤ n) : Integrable (sphereOverlapShape n) := by
  apply (sphereOverlapShape_continuous n).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro q hq
  by_contra h
  apply hq
  exact sphereOverlapShape_eq_zero hn (by
    rw [Set.mem_Icc,not_and_or] at h
    rcases h with h | h <;> have ha := le_abs_self q <;> have hb := neg_le_abs q <;> linarith)

lemma overlapShape_normalizer_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < ∫ q : ℝ, sphereOverlapShape n q := by
  apply (sphereOverlapShape_continuous n).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1))
    intro q hq
    by_contra h
    apply hq
    exact sphereOverlapShape_eq_zero hn (by
      rw [Set.mem_Icc,not_and_or] at h
      rcases h with h | h <;> have ha := le_abs_self q <;> have hb := neg_le_abs q <;> linarith)
  · exact sphereOverlapShape_nonneg n
  · norm_num [sphereOverlapShape]

lemma sphereOverlapShape_log_variation {n : ℕ} (hn : 3 ≤ n) {q r a δ : ℝ}
    (ha : a ≤ 1/2) (hq : |q| ≤ a) (hr : |r| ≤ a) (hδ : |r-q| ≤ δ) :
    |Real.log (sphereOverlapShape n r)-Real.log (sphereOverlapShape n q)| ≤
      2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ := by
  have ha0 : 0 ≤ a := (abs_nonneg q).trans hq
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hq2 : q^2 ≤ a^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ a+|q| by positivity), sq_abs q]
  have hr2 : r^2 ≤ a^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ a+|r| by positivity), sq_abs r]
  have hq4 : q^4 ≤ a^4 := by nlinarith [sq_nonneg (a^2-q^2)]
  have hr4 : r^4 ≤ a^4 := by nlinarith [sq_nonneg (a^2-r^2)]
  have hsum : |r+q| ≤ 2*a := (abs_add_le _ _).trans (by linarith)
  have hdiff : |r^2-q^2| ≤ δ*(2*a) := by
    rw [show r^2-q^2=(r-q)*(r+q) by ring, abs_mul]
    exact mul_le_mul hδ hsum (abs_nonneg _) hd0
  have hqe := sphereOverlapShape_log_error hn (hq.trans ha)
  have hre := sphereOverlapShape_log_error hn (hr.trans ha)
  have hid : Real.log (sphereOverlapShape n r)-Real.log (sphereOverlapShape n q) =
      (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2)-
      (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)-(n:ℝ)/2*(r^2-q^2) := by ring
  rw [hid]
  calc
    _ ≤ |Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2| +
        |Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2| + |(n:ℝ)/2*(r^2-q^2)| :=
      by
        have h₁ := abs_sub (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2 - (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)) ((n:ℝ)/2*(r^2-q^2))
        have h₂ := abs_sub (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2) (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)
        linarith
    _ ≤ ((n:ℝ)*r^4+2*r^2)+((n:ℝ)*q^4+2*q^2)+((n:ℝ)/2)*(δ*(2*a)) := by
      rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)/2)]
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hq4),
        mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hr4)]

lemma sphereOverlapDensity_variation {n : ℕ} (hn : 4 ≤ n) {q r a δ : ℝ}
    (ha : a ≤ 1/2) (hq : |q| ≤ a) (hr : |r| ≤ a) (hδ : |r-q| ≤ δ) :
    sphereOverlapDensity n q * Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ)) ≤
      sphereOverlapDensity n r := by
  have h := (abs_le.mp (sphereOverlapShape_log_variation (n:=n) (by omega) ha hq hr hδ)).1
  have hqp := sphereOverlapShape_pos (n:=n) (hq.trans_lt (ha.trans_lt (by norm_num)))
  have hrp := sphereOverlapShape_pos (n:=n) (hr.trans_lt (ha.trans_lt (by norm_num)))
  have he := Real.exp_le_exp.mpr (show Real.log (sphereOverlapShape n q)-
    (2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ) ≤ Real.log (sphereOverlapShape n r) by linarith)
  rw [Real.exp_sub,Real.exp_log hqp,Real.exp_log hrp,div_eq_mul_inv,← Real.exp_neg] at he
  unfold sphereOverlapDensity
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right he (overlapShape_normalizer_pos hn).le

def outwardBinLeft (δ q : ℝ) : ℝ := if q < 0 then q-δ else if 0 < q then q else -δ/2

def outwardBin (δ q : ℝ) : Set ℝ := Ioc (outwardBinLeft δ q) (outwardBinLeft δ q+δ)

lemma outwardBin_distance {δ q r : ℝ} (_hδ : 0 ≤ δ) (hr : r ∈ outwardBin δ q) :
    |r-q| ≤ δ ∧ |q| ≤ |r| := by
  unfold outwardBin outwardBinLeft at hr
  split_ifs at hr with hq hq
  · rw [Set.mem_Ioc] at hr
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_neg hq,abs_of_nonpos (by linarith : r ≤ 0)]; linarith
  · rw [Set.mem_Ioc] at hr
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_pos hq,abs_of_nonneg (by linarith : 0 ≤ r)]; linarith
  · have hq0 : q=0 := by linarith
    rw [Set.mem_Ioc] at hr
    constructor
    · rw [hq0,sub_zero,abs_le]; constructor <;> linarith
    · rw [hq0,abs_zero]; exact abs_nonneg _

lemma outwardBin_separated {δ q r : ℝ} (hδ : 0 < δ) (hqr : q+δ ≤ r) :
    outwardBinLeft δ q+δ ≤ outwardBinLeft δ r := by
  unfold outwardBinLeft
  split_ifs <;> linarith

lemma outwardBin_disjoint {δ q r : ℝ} (hδ : 0 < δ) (hqr : q+δ ≤ r) :
    Disjoint (outwardBin δ q) (outwardBin δ r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hb := outwardBin_separated hδ hqr
  have hx' := (show x ∈ Set.Ioc _ _ from hx).2
  have hy' := (show x ∈ Set.Ioc _ _ from hy).1
  linarith

lemma sphereOverlapDensity_nonneg (n : ℕ) (q : ℝ) : 0 ≤ sphereOverlapDensity n q := by
  exact div_nonneg (sphereOverlapShape_nonneg _ _) (integral_nonneg (sphereOverlapShape_nonneg n))

lemma sphereOverlapDensity_continuous (n : ℕ) : Continuous (sphereOverlapDensity n) :=
  (sphereOverlapShape_continuous n).div_const _

lemma sphereOverlapDensity_mul_integrable {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun q => h q*sphereOverlapDensity n q) := by
  apply (hh.mul (sphereOverlapDensity_continuous n)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro q hq
  by_contra hnq
  apply hq
  have : sphereOverlapShape n q = 0 := sphereOverlapShape_eq_zero hn (by
    rw [Set.mem_Icc,not_and_or] at hnq
    rcases hnq with h | h <;> have ha := le_abs_self q <;> have hb := neg_le_abs q <;> linarith)
  change h q * sphereOverlapDensity n q = 0
  rw [sphereOverlapDensity,this,zero_div,mul_zero]

lemma outwardBin_integral_const (δ q c : ℝ) (hδ : 0 ≤ δ) :
    (∫ _ : ℝ in outwardBin δ q, c) = δ*c := by
  rw [integral_const,measureReal_restrict_apply_univ,outwardBin,Real.volume_real_Ioc]
  simp only [add_sub_cancel_left,max_eq_left hδ,smul_eq_mul]

lemma outwardBin_integral_lower {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ r, 0 ≤ h r) (hm : ∀ q r, |q| ≤ |r| → h q ≤ h r)
    {a δ q : ℝ} (hδ : 0 ≤ δ) (ha : a ≤ 1/2) (hq : |q|+δ ≤ a) :
    δ*(h q*sphereOverlapDensity n q*Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ))) ≤
      ∫ r in outwardBin δ q, h r*sphereOverlapDensity n r := by
  rw [← outwardBin_integral_const δ q _ hδ]
  apply setIntegral_mono_on continuous_const.integrableOn_Ioc
    ((hc.mul (sphereOverlapDensity_continuous n)).integrableOn_Ioc) measurableSet_Ioc
  intro r hr
  obtain ⟨hd,hmr⟩ := outwardBin_distance hδ hr
  have hra : |r| ≤ a := by
    have hl : |r| ≤ |r-q|+|q| := by simpa only [sub_add_cancel] using abs_add_le (r-q) q
    linarith
  have hvar := sphereOverlapDensity_variation hn ha (show |q| ≤ a by linarith) hra hd
  calc
    _ = h q*(sphereOverlapDensity n q*Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ))) := by ring
    _ ≤ h r*sphereOverlapDensity n r := mul_le_mul (hm q r hmr) hvar (mul_nonneg (sphereOverlapDensity_nonneg n q) (Real.exp_pos _).le) (h0 r)

lemma latticeOverlap_spacing {n j k : ℕ} (hn : 0 < n) (hjk : j < k) :
    latticeOverlap n j+2/(n:ℝ) ≤ latticeOverlap n k := by
  have h : (j:ℝ)+1 ≤ k := by exact_mod_cast hjk
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold latticeOverlap
  have hd := div_le_div_of_nonneg_right (show 2*(j:ℝ)+2 ≤ 2*k by linarith) hnR.le
  rw [add_div] at hd
  linarith

lemma outwardBin_lattice_disjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (fun j k : ℕ => Disjoint (outwardBin (2/(n:ℝ)) (latticeOverlap n j))
      (outwardBin (2/(n:ℝ)) (latticeOverlap n k))) := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact outwardBin_disjoint (by positivity) (latticeOverlap_spacing hn hjk)
  · exact (outwardBin_disjoint (by positivity) (latticeOverlap_spacing hn hkj)).symm

lemma outwardBin_sum_integral_le {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ q, 0 ≤ h q) (t : Finset ℕ) :
    (∑ j ∈ t, ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r) ≤
      ∫ r : ℝ, h r*sphereOverlapDensity n r := by
  rw [← integral_biUnion_finset t (s := fun j => outwardBin (2/(n:ℝ)) (latticeOverlap n j)) (fun _ _ => measurableSet_Ioc)
    (fun _ _ _ _ hjk => outwardBin_lattice_disjoint (n:=n) (by omega) hjk)
    (fun _ _ => (sphereOverlapDensity_mul_integrable hn hc).integrableOn)]
  apply setIntegral_le_integral (sphereOverlapDensity_mul_integrable hn hc)
  exact ae_of_all _ (fun q => mul_nonneg (h0 q) (sphereOverlapDensity_nonneg n q))

lemma central_overlap_sum_bound {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ r, 0 ≤ h r) (hm : ∀ q r, |q| ≤ |r| → h q ≤ h r)
    {a e : ℝ} (ha : a ≤ 1/2) (he : 0 ≤ e) (t : Finset ℕ)
    (ht : ∀ j ∈ t, |latticeOverlap n j|+2/(n:ℝ) ≤ a)
    (hp : ∀ j ∈ t, cubeOverlapMass n j ≤ (1+e)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j)) :
    (∑ j ∈ t, cubeOverlapMass n j*h (latticeOverlap n j)) ≤
      (1+e)*Real.exp (2*(n:ℝ)*a^4+4*a^2+2*a) * ∫ r : ℝ, h r*sphereOverlapDensity n r := by
  have hnR : (n:ℝ)≠0 := by positivity
  have hE : (n:ℝ)*a*(2/(n:ℝ))=2*a := by field_simp
  let C := (1+e)*Real.exp (2*(n:ℝ)*a^4+4*a^2+2*a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j ∈ t, C * ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r := by
      apply Finset.sum_le_sum
      intro j hj
      have hbin := outwardBin_integral_lower hn hc h0 hm (by positivity) ha (ht j hj)
      rw [hE] at hbin
      have hi := mul_le_mul_of_nonneg_left hbin hC
      have hid : C * ((2/(n:ℝ))*(h (latticeOverlap n j)*sphereOverlapDensity n (latticeOverlap n j)*
          Real.exp (-(2*(n:ℝ)*a^4+4*a^2+2*a)))) =
          ((1+e)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))*h (latticeOverlap n j) := by
        dsimp [C]
        rw [Real.exp_neg]
        field_simp
      rw [hid] at hi
      exact (mul_le_mul_of_nonneg_right (hp j hj) (h0 _)).trans hi
    _ = C * (∑ j ∈ t, ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (outwardBin_sum_integral_le hn hc h0 t) hC

lemma overlap_bin_error_tendsto {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) :
    Tendsto (fun n : ℕ => 2*(n:ℝ)*(c n+2/(n:ℝ))^4+4*(c n+2/(n:ℝ))^2+
      2*(c n+2/(n:ℝ))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => c n+2/(n:ℝ)) atTop (𝓝 0) := by simpa using hc.add hd
  have hfour : Tendsto (fun n : ℕ => (n:ℝ)*(c n+2/(n:ℝ))^4) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ (show Tendsto (fun n : ℕ => 81*((n:ℝ)*c n^4)) atTop (𝓝 0) from by simpa using hc4.const_mul 81)
    filter_upwards [hcmin] with n hn
    have hc0 : 0 ≤ c n := (by positivity : 0 ≤ 1/(n:ℝ)).trans hn
    have hδ : 2/(n:ℝ) ≤ 2*c n := by
      calc
        2/(n:ℝ) = 2*(1/(n:ℝ)) := by ring
        _ ≤ 2*c n := mul_le_mul_of_nonneg_left hn (by norm_num)
    have h := pow_le_pow_left₀ (show 0 ≤ c n+2/(n:ℝ) by positivity) (show c n+2/(n:ℝ) ≤ 3*c n by linarith) 4
    have hi := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    nlinarith
  convert ((hfour.const_mul 2).add ((ha.pow 2).const_mul 4)).add (ha.const_mul 2) using 1
  · ext n; ring
  · norm_num

lemma central_overlap_uniform_bound {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℝ → ℝ, Continuous h → (∀ q, 0 ≤ h q) →
      (∀ q r, |q| ≤ |r| → h q ≤ h r) →
      (∑ j ∈ (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ c n),
        cubeOverlapMass n j*h (latticeOverlap n j)) ≤
          (1+ε)*∫ r : ℝ, h r*sphereOverlapDensity n r := by
  have hd : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => c n+2/(n:ℝ)) atTop (𝓝 0) := by simpa using hc.add hd
  have hfac : Tendsto (fun n : ℕ => (1+ε/2)*Real.exp (2*(n:ℝ)*(c n+2/(n:ℝ))^4+
      4*(c n+2/(n:ℝ))^2+2*(c n+2/(n:ℝ)))) atTop (𝓝 (1+ε/2)) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp (overlap_bin_error_tendsto hc hc4 hcmin)).const_mul (1+ε/2)
  have hfe := hfac.eventually (eventually_le_nhds (show 1+ε/2 < 1+ε by linarith))
  have hae := ha.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2))
  have hpe := cube_sphere_overlap_uniform hc hc4 hcmin (ε/2) (by linarith)
  filter_upwards [eventually_ge_atTop 4,hfe,hae,hpe] with n hn hf ha hp
  intro h hcont h0 hmono
  classical
  let t := (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ c n)
  have hbin := central_overlap_sum_bound hn hcont h0 hmono ha (show 0 ≤ ε/2 by linarith) t
    (fun j hj => by have := (Finset.mem_filter.mp hj).2; linarith)
  have hmass : ∀ j ∈ t, cubeOverlapMass n j ≤
      (1+ε/2)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j) := by
    intro j hj
    have hjR := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hjq := (Finset.mem_filter.mp hj).2
    have hq : |latticeOverlap n j| < 1 := by
      have : 0 ≤ 2/(n:ℝ) := by positivity
      linarith
    have hpos : 0 < (2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j) :=
      mul_pos (by positivity) (div_pos (sphereOverlapShape_pos hq) (overlapShape_normalizer_pos hn))
    have hh := (abs_lt.mp (hp j (by omega) hjq)).2
    have hh' : cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j)) ≤ 1+ε/2 := by linarith
    simpa only [mul_assoc] using (div_le_iff₀ hpos).mp hh'
  exact (hbin hmass).trans (mul_le_mul_of_nonneg_right hf (integral_nonneg (fun q => mul_nonneg (h0 q) (sphereOverlapDensity_nonneg n q))))

def overlapCentralCutoff (n : ℕ) : ℝ := (n:ℝ)^(-(7/24:ℝ))

lemma overlapCentralCutoff_tendsto : Tendsto overlapCentralCutoff atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/24)).comp tendsto_natCast_atTop_atTop

lemma overlapCentralCutoff_fourth :
    Tendsto (fun n : ℕ => (n:ℝ)*overlapCentralCutoff n^4) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_apply,overlapCentralCutoff]
  have hpow : ((n:ℝ)^(-(7/24:ℝ)))^4 = (n:ℝ)^(-(7/24:ℝ)*(4:ℝ)) := by
    rw [Real.rpow_mul (by positivity)]
    norm_num
  rw [hpow]
  conv_rhs => lhs; rw [← Real.rpow_one (n:ℝ)]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  norm_num

lemma overlapCentralCutoff_min : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ overlapCentralCutoff n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold overlapCentralCutoff
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

open MeasureTheory Set

lemma integral_shape_on_Ioo {n : ℕ} (hn : 4 ≤ n) (h : ℝ → ℝ) :
    (∫ q in Ioo (-1:ℝ) 1, h q*sphereOverlapShape n q) = ∫ q, h q*sphereOverlapShape n q := by
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Ioo (-1:ℝ) 1
  · simp only [indicator_of_mem hq]
  · have hqs : 1 ≤ |q| := by
      rw [Set.mem_Ioo,not_and_or] at hq
      rcases hq with hq | hq
      · exact (le_neg_of_le_neg (le_of_not_gt hq)).trans (neg_le_abs q)
      · exact (le_of_not_gt hq).trans (le_abs_self q)
    simp only [indicator_of_notMem hq,sphereOverlapShape_eq_zero hn hqs,mul_zero]

lemma overlapShapeMeasure_real_univ {n : ℕ} (hn : 4 ≤ n) :
    (overlapShapeMeasure n Set.univ).toReal = ∫ q, sphereOverlapShape n q := by
  rw [overlapShapeMeasure_univ,← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (sphereOverlapShape_nonneg n))
    (sphereOverlapShape_continuous n).aestronglyMeasurable]
  simpa only [one_mul] using integral_shape_on_Ioo hn (fun _ => 1)

lemma normalizedOverlapShape_integral {n : ℕ} (hn : 4 ≤ n) (h : ℝ → ℝ) :
    (∫ q, h q ∂normalizedOverlapShape n) = ∫ q, h q*sphereOverlapDensity n q := by
  rw [normalizedOverlapShape,integral_smul_measure,ENNReal.toReal_inv,
    overlapShapeMeasure_real_univ hn]
  rw [overlapShapeMeasure,integral_withDensity_eq_integral_toReal_smul
    (by unfold sphereOverlapShape; fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (sphereOverlapShape_nonneg _ _), smul_eq_mul]
  simp_rw [mul_comm (sphereOverlapShape n _)]
  rw [integral_shape_on_Ioo hn,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  unfold sphereOverlapDensity
  ring

lemma sphereOverlap_density_second_moment (n : ℕ) (lam : Fin (n+4) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+4))} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, pairMoment lam u v q*sphereOverlapDensity (n+4) q) = spherePartition lam 1 r^2 := by
  rw [← normalizedOverlapShape_integral (by omega : 4 ≤ n+4),← sphereOverlapLaw_density (n+1)]
  exact sphereOverlap_second_moment lam hu hv horth

lemma rotatedCubePartition_second_lattice {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n) (hv : ‖v‖ = Real.sqrt n)
    (horth : inner ℝ u v = 0) :
    (∫ U, rotatedCubePartition lam 1 U ^ 2 ∂orthogonalHaar (Fin n)) =
      ∑ j ∈ Finset.range (n+1), cubeOverlapMass n j*pairMoment lam u v (latticeOverlap n j) := by
  rw [rotatedCubePartition_second_moment hn lam hu hv horth,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cubeOverlapMass,latticeOverlap,mul_assoc]

lemma normalized_integral_square {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Continuous f) {S : ℝ} (hS : S ≠ 0) (hm : ∫ x, f x ∂μ = S) :
    (∫ x, (f x/S-1)^2 ∂μ) = (∫ x, f x^2 ∂μ)/S^2-1 := by
  have hi : Integrable f μ := by simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ
  have hi2 : Integrable (fun x => f x^2) μ := by simpa only [integrableOn_univ] using (show Continuous (fun x => f x^2) from hf.pow 2).continuousOn.integrableOn_compact isCompact_univ
  have he (x : Ω) : (f x/S-1)^2 = f x^2/S^2-2*(f x/S)+1 := by ring
  simp_rw [he]
  have his : Integrable (fun x => f x^2/S^2-2*(f x/S)) μ :=
    (hi2.div_const (S^2)).sub ((hi.div_const S).const_mul 2)
  rw [integral_add his (integrable_const (1:ℝ)),
    integral_sub (hi2.div_const (S^2)) ((hi.div_const S).const_mul 2),
    integral_div,integral_const_mul,integral_div,hm,div_self hS,integral_const,probReal_univ,one_smul]
  ring

end CriticalSK

end

end OAI
