import OAI.Probability.GaussianPropeller.FourAlgebra

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller
namespace Scalar

def charge (A u : ℝ) : ℝ := 0.415 * u - (A - 0.15) * u ^ 2

theorem third_radius_gt {L u : ℝ} (hu : 0 < u) (hL : L ≤ 8 / 9)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116) : 0.23 < u := by
  by_contra! h
  have hd : (0.415 : ℝ) / 0.23 ≤ 0.415 / u :=
    div_le_div_of_nonneg_left (by norm_num) hu h
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  norm_num at hm
  nlinarith

theorem small_minimum_interval {L u t a b M : ℝ}
    (ht : 0 ≤ t) (htq : t ≤ 0.066) (hL : L ≤ 8 / 9)
    (hua : a ≤ u) (hub : u ≤ b) (ha : 0.066 < a)
    (hden : 0 < 0.415 / b - 0.734) (hM : 0 ≤ M)
    (hrow : (0.116 : ℝ) ≤
      (1 - (b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M)) * (0.415 / b - 0.734))
    (hmargin : 8 * (0.066 : ℝ) ^ 2 < (a ^ 2 - (0.066 : ℝ) ^ 2) * M)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) : False := by
  have hup : 0 < u := by linarith
  have hb : 0 < b := lt_of_lt_of_le hup hub
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 0.415 by norm_num) hup hub
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  have hLc : b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M ≤ L := by
    have hh := le_of_mul_le_mul_right ((hm.trans hcharge).trans hrow) hden
    linarith
  have hub2 : u ^ 2 ≤ b ^ 2 := by nlinarith
  have hua2 : a ^ 2 ≤ u ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
  have hfirst : a ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
  have hfirst0 : 0 ≤ u ^ 2 - t ^ 2 := by nlinarith
  have hsecond : M ≤ L - u ^ 2 - 2 * t ^ 2 := by linarith
  have hp := mul_le_mul hfirst hsecond hM hfirst0
  nlinarith

theorem minimum_gt {L u t : ℝ} (ht : 0 ≤ t) (hu : 0.23 < u)
    (hL : L ≤ 8 / 9) (hL2 : 2 * u ^ 2 ≤ L)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) :
    0.066 < t := by
  by_contra! htq
  by_cases hbig : 0.44 ≤ u
  · have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
    have hu2 : (0.44 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith
    have hfirst : (0.44 : ℝ) ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
    have hsecond : (0.44 : ℝ) ^ 2 - 2 * (0.066 : ℝ) ^ 2 ≤
        L - u ^ 2 - 2 * t ^ 2 := by linarith
    have hp := mul_le_mul hfirst hsecond (by norm_num)
      (show 0 ≤ u ^ 2 - t ^ 2 by nlinarith)
    norm_num at hp
    nlinarith
  · have hb : u ≤ 0.44 := le_of_lt (lt_of_not_ge hbig)
    by_cases h30 : u ≤ 0.30
    · exact small_minimum_interval (a := 0.23) (b := 0.30) (M := 0.72264)
        ht htq hL hu.le h30 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h35 : u ≤ 0.35
    · exact small_minimum_interval (a := 0.30) (b := 0.35) (M := 0.61198)
        ht htq hL (by linarith) h35 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h41 : u ≤ 0.41
    · exact small_minimum_interval (a := 0.35) (b := 0.41) (M := 0.40621)
        ht htq hL (by linarith) h41 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    · exact small_minimum_interval (a := 0.41) (b := 0.44) (M := 0.24314)
        ht htq hL (by linarith) hb (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet

theorem first_constraint_rational {L c t : ℝ}
    (h : (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * (3 / Real.pi) ^ 2 * t ^ 2) :
    (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * t ^ 2 := by
  have hratio : (3 : ℝ) / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).mpr Real.pi_gt_three.le
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hsq : ((3 : ℝ) / Real.pi) ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  nlinarith

theorem final_contradiction {c t : ℝ} (ht : 0 < t) (ht12 : t < 0.12)
    (hc : 2.6 * t < c)
    (hdet : (3 / 2 : ℝ) * (c - t ^ 2) ^ 2 ≤ 10 * (3 / Real.pi) ^ 2 * t ^ 2) :
    False := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hratio : (3 : ℝ) / Real.pi < 150 / 157 := by
    rw [div_lt_iff₀ hp]
    nlinarith [Real.pi_gt_d2]
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hratio2 : ((3 : ℝ) / Real.pi) ^ 2 < (150 / 157 : ℝ) ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have htop := mul_lt_mul_of_pos_right hratio2 ht2
  have hc' : (2.48 : ℝ) * t < c - t ^ 2 := by nlinarith
  have hcsq : ((2.48 : ℝ) * t) ^ 2 < (c - t ^ 2) ^ 2 := by nlinarith
  nlinarith

theorem charge_concave {A : ℝ} (hA : 0.15 ≤ A) :
    ConcaveOn ℝ Set.univ (charge A) := by
  have hlin : ConcaveOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (0.415 : ℝ) * u) :=
    (concaveOn_id convex_univ).smul (by norm_num)
  have hquad : ConvexOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (A - 0.15) * u ^ 2) :=
    (Even.convexOn_pow (by decide : Even (2 : ℕ))).smul (by linarith)
  exact hlin.sub hquad

theorem min_charge_le {A a b u : ℝ} (hA : 0.15 ≤ A)
    (ha : a ≤ u) (hb : u ≤ b) : min (charge A a) (charge A b) ≤ charge A u :=
  (charge_concave hA).min_le_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨ha, hb⟩

noncomputable def finalBudget (A k t : ℝ) : ℝ :=
  charge A (Real.sqrt (2.6 * t)) + k * charge A t

theorem finalBudget_concave {A k : ℝ} (hA : 0.15 ≤ A) (hk : 0 ≤ k) :
    ConcaveOn ℝ (Set.Ici 0) (finalBudget A k) := by
  have hsqrt : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ =>
      (0.415 * Real.sqrt 2.6) * Real.sqrt t) :=
    Real.strictConcaveOn_sqrt.concaveOn.smul (by positivity)
  have hlin : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => (2.6 * (A - 0.15)) * t) :=
    (convexOn_id (convex_Ici (0 : ℝ))).smul (by positivity)
  have hquad := ((charge_concave hA).subset (Set.subset_univ _) (convex_Ici 0)).smul hk
  have heq : Set.EqOn
      (fun t : ℝ => (0.415 * Real.sqrt 2.6) * Real.sqrt t -
        (2.6 * (A - 0.15)) * t + k * charge A t)
      (finalBudget A k) (Set.Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hsq := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
    dsimp [finalBudget, charge]
    rw [hsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2.6)]
    ring
  exact ((hsqrt.sub hlin).add hquad).congr heq

theorem clipped_charge {A s q u δ : ℝ} (hd : 0 < A - 0.15) (hs : 0 < s)
    (hq : 0 ≤ q) (hqu : q ≤ u) (hds : (A - 0.15) * s = 0.415)
    (hδ0 : 0 ≤ δ) (hδ : charge A u ≤ δ) :
    (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) ≤ δ := by
  have hden : 0 < s + q := by positivity
  have hcoef : 0 ≤ (A - 0.15) * q / (s + q) := by positivity
  by_cases hu : s ≤ u
  · have hsq : s ^ 2 - u ^ 2 ≤ 0 := by nlinarith
    exact (mul_nonpos_of_nonneg_of_nonpos hcoef hsq).trans hδ0
  · have hu' : u ≤ s := le_of_lt (lt_of_not_ge hu)
    have hprod : 0 ≤ (A - 0.15) * s * ((s - u) * (u - q)) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hqu))
    have hdiff : 0 ≤ charge A u -
        (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) := by
      have heq : (charge A u - (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2)) *
          (s + q) = (A - 0.15) * s * ((s - u) * (u - q)) := by
        dsimp [charge]
        rw [← hds]
        field_simp
        ring
      exact nonneg_of_mul_nonneg_left (heq.symm ▸ hprod) hden
    linarith

noncomputable def smallRoot (A k : ℝ) : ℝ :=
  (0.415 - Real.sqrt (0.415 ^ 2 - 4 * (A - 0.15) * (1 - A) / k)) /
    (2 * (A - 0.15))

noncomputable def threshold (A : ℝ) : ℝ := 0.415 / (A - 0.15)

noncomputable def clipCoeff (A : ℝ) : ℝ := (A - 0.15) * 0.42 / (threshold A + 0.42)

theorem smallRoot_five :
    0.066 < smallRoot 0.929 2 ∧ smallRoot 0.929 2 < 0.109 ∧
    2 * charge 0.929 (smallRoot 0.929 2) = 1 - 0.929 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61607 / 1000000)
  have hnn := Real.sqrt_nonneg (61607 / 1000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem smallRoot_six :
    0.066 < smallRoot 0.884 3 ∧ smallRoot 0.884 3 < 0.12 ∧
    3 * charge 0.884 (smallRoot 0.884 3) = 1 - 0.884 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 176099 / 3000000)
  have hnn := Real.sqrt_nonneg (176099 / 3000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

structure Regime (A : ℝ) (k : ℕ) : Prop where
  A_lower : 0.884 ≤ A
  A_upper : A < 1
  k_lower : 2 ≤ k
  root_lower : 0.066 < smallRoot A k
  root_upper : smallRoot A k < 0.12
  root_eq : (k : ℝ) * charge A (smallRoot A k) = 1 - A
  root_cap : 2.6 * smallRoot A k < (threshold A) ^ 2
  root_slope : (A - 0.15) * (0.42 + smallRoot A k) < 0.415
  cap_charge : 1 - A < (k : ℝ) * charge A 0.42
  tail_end_charge : charge A 0.066 ≤ charge A 0.45
  base_charge_pos : 0 < charge A 0.066
  four_margin : 1 - A < clipCoeff A *
      (4 * (threshold A) ^ 2 - 1 + ((k : ℝ) - 1) * 0.066 ^ 2) +
      ((k : ℝ) - 1) * charge A 0.066
  third_margin : 1 - A < charge A 0.23 + (k : ℝ) * charge A 0.066
  final_margin : 1 - A < finalBudget A k 0.066

theorem regime_five : Regime 0.929 2 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_five
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · simpa using hu.trans (by norm_num : (0.109 : ℝ) < 0.12)
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

theorem regime_six : Regime 0.884 3 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_six
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · exact hu
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

structure RadiusData (m : ℕ) (A : ℝ) where
  r : ℕ → ℝ
  δ : ℕ → ℝ
  pos : ∀ i < m, 0 < r i
  ordered : AntitoneOn r (Set.Iio m)
  cap : ∀ i < m, r i ≤ 2 / 3
  norm : ∑ i ∈ Finset.range m, r i ^ 2 = 1
  nonneg : ∀ i < m, 0 ≤ δ i
  lower : ∀ i < m, charge A (r i) ≤ δ i
  budget : ∑ i ∈ Finset.range m, δ i = 1 - A

theorem sum_split (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, f i) + (∑ i ∈ Finset.range (m - p), f (p + i)) =
      ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_range_add, Nat.add_sub_of_le hp]

theorem sum_prefix_le (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m)
    (hf : ∀ i < m, 0 ≤ f i) :
    (∑ i ∈ Finset.range p, f i) ≤ ∑ i ∈ Finset.range m, f i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
    (fun i hi _ => hf i (Finset.mem_range.mp hi))

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem minimum_le {i : ℕ} (hi : i < m) : D.r (m - 1) ≤ D.r i :=
  D.radius_le (by omega) (by omega)

theorem prefix_norm {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) ≤ 1 := by
  simpa [D.norm] using sum_prefix_le (fun i => D.r i ^ 2) hp (fun i _ => sq_nonneg _)

theorem prefix_budget {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) ≤ 1 - A := by
  simpa [D.budget] using sum_prefix_le D.δ hp D.nonneg

theorem first_two_cap (hm : 2 ≤ m) : D.r 0 ^ 2 + D.r 1 ^ 2 ≤ 8 / 9 := by
  have h0 := D.cap 0 (by omega)
  have h1 := D.cap 1 (by omega)
  have hp0 := D.pos 0 (by omega)
  have hp1 := D.pos 1 (by omega)
  nlinarith

theorem third_twice (hm : 3 ≤ m) : 2 * D.r 2 ^ 2 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by
  have hp := D.pos 2 (by omega)
  have h0 := D.radius_le (by omega : 2 < m) (by omega : 0 ≤ 2)
  have h1 := D.radius_le (by omega : 2 < m) (by omega : 1 ≤ 2)
  nlinarith

theorem common_charge (hm : 3 ≤ m) (hA : 0.884 ≤ A) :
    (1 - (D.r 0 ^ 2 + D.r 1 ^ 2)) * (0.415 / D.r 2 - 0.734) ≤ 0.116 := by
  let u := D.r 2
  have hu : 0 < u := D.pos 2 (by omega)
  have hterm : ∀ i < m - 2,
      D.r (2 + i) ^ 2 * (0.415 / u - (A - 0.15)) ≤ D.δ (2 + i) := by
    intro i hi
    have hi' : 2 + i < m := by omega
    have hri := D.pos (2 + i) hi'
    have hle : D.r (2 + i) ≤ u := D.radius_le hi' (by omega)
    have hmul : D.r (2 + i) ^ 2 * (0.415 / u) ≤ 0.415 * D.r (2 + i) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hu).mpr
      nlinarith [mul_nonneg (le_of_lt hri) (sub_nonneg.mpr hle)]
    have hlower := D.lower (2 + i) hi'
    dsimp [charge] at hlower
    nlinarith
  have hsum := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  rw [← Finset.sum_mul] at hsum
  have hn := sum_split (fun i => D.r i ^ 2) (by omega : 2 ≤ m)
  have hb := sum_split D.δ (by omega : 2 ≤ m)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn hb
  rw [D.norm] at hn
  rw [D.budget] at hb
  have hd0 := D.nonneg 0 (by omega)
  have hd1 := D.nonneg 1 (by omega)
  have hL : 0 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by positivity
  have hAdj : 0 ≤ (A - 0.884) * (D.r 0 ^ 2 + D.r 1 ^ 2) := by positivity
  have hns : (∑ i ∈ Finset.range (m - 2), D.r (2 + i) ^ 2) =
      1 - (D.r 0 ^ 2 + D.r 1 ^ 2) := by linarith
  rw [hns] at hsum
  dsimp [u] at hsum
  nlinarith

theorem tail_coarse_cap (hm : 5 ≤ m) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    D.r i ≤ 0.45 := by
  have hn := D.prefix_norm (by omega : 5 ≤ m)
  have hp := D.pos i hi
  have h0 := D.radius_le hi (by omega : 0 ≤ i)
  have h1 := D.radius_le hi (by omega : 1 ≤ i)
  have h2 := D.radius_le hi (by omega : 2 ≤ i)
  have h3 := D.radius_le hi (by omega : 3 ≤ i)
  have h4 := D.radius_le hi hi4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn
  nlinarith

theorem block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    ∑ i ∈ Finset.range q, D.δ (p + i) ≤ 1 - A := by
  have h := D.prefix_budget hpq
  have hs := sum_split D.δ (by omega : p ≤ p + q)
  rw [Nat.add_sub_cancel_left] at hs
  have hn : 0 ≤ ∑ i ∈ Finset.range p, D.δ i :=
    Finset.sum_nonneg (fun i hi => D.nonneg i (by have := Finset.mem_range.mp hi; omega))
  linarith

theorem prefix_block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) +
      (∑ i ∈ Finset.range q, D.δ (p + i)) ≤ 1 - A := by
  rw [← Finset.sum_range_add]
  exact D.prefix_budget hpq

theorem prefix_block_norm {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) +
      (∑ i ∈ Finset.range q, D.r (p + i) ^ 2) ≤ 1 := by
  rw [← Finset.sum_range_add]
  exact D.prefix_norm hpq

theorem minimum_lower (hm : 5 ≤ m) (hA : 0.884 ≤ A)
    (hdet : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) :
    0.066 < D.r (m - 1) := by
  have hc := D.common_charge (by omega) hA
  have hL := D.first_two_cap (by omega)
  have hu := third_radius_gt (D.pos 2 (by omega)) hL hc
  exact minimum_gt (D.pos (m - 1) (by omega)).le hu hL
    (D.third_twice (by omega)) hc (first_constraint_rational hdet)

theorem tail_base_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    charge A 0.066 ≤ D.δ i := by
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (ht.le.trans (D.minimum_le hi)) (D.tail_coarse_cap hm hi hi4)
  rw [min_eq_left R.tail_end_charge] at h
  exact h.trans (D.lower i hi)

theorem fourth_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : D.r 3 ≤ 0.42 := by
  by_contra! h4
  have hk : 2 ≤ k := R.k_lower
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hs : 0 < threshold A := div_pos (by norm_num) hd
  have hds : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hcoef : 0 ≤ clipCoeff A := by unfold clipCoeff; positivity
  have hfirst : ∀ i < 4,
      clipCoeff A * ((threshold A) ^ 2 - D.r i ^ 2) ≤ D.δ i := by
    intro i hi
    have hi' : i < m := by omega
    exact clipped_charge hd hs (by norm_num)
      (h4.le.trans (D.radius_le (by omega : 3 < m) (by omega)))
      hds (D.nonneg i hi') (D.lower i hi')
  have hf := Finset.sum_le_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hf
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hf
  have htailnorm : (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range (k - 1), D.r (4 + i) ^ 2 := by
    have hterm : ∀ i < k - 1, (0.066 : ℝ) ^ 2 ≤ D.r (4 + i) ^ 2 := by
      intro i hi
      have hi' : 4 + i < m := by omega
      have hr := ht.trans_le (D.minimum_le hi')
      nlinarith
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hn := D.prefix_block_norm (by omega : 4 + (k - 1) ≤ m)
  have hnm : (∑ i ∈ Finset.range 4, D.r i ^ 2) ≤
      1 - (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 := by linarith
  have hf' := mul_le_mul_of_nonneg_left (sub_le_sub_left hnm (4 * (threshold A) ^ 2)) hcoef
  have htbudget : (k - 1 : ℕ) * charge A 0.066 ≤
      ∑ i ∈ Finset.range (k - 1), D.δ (4 + i) := by
    have hterm : ∀ i < k - 1, charge A 0.066 ≤ D.δ (4 + i) := by
      intro i hi
      exact D.tail_base_charge R hm ht (by omega) (by omega)
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hb := D.prefix_block_budget (by omega : 4 + (k - 1) ≤ m)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast] at hf' htbudget
  have hmarg := R.four_margin
  nlinarith

theorem tail_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    D.r i ≤ 0.42 :=
  (D.radius_le hi hi3).trans (D.fourth_cap R hm hkm ht)

theorem minimum_charge_bound {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    (k : ℝ) * charge A (D.r (m - 1)) ≤ 1 - A := by
  have hterm : ∀ i < k,
      min (charge A (D.r (m - 1))) (charge A 0.42) ≤ D.δ (3 + i) := by
    intro i hi
    have hi' : 3 + i < m := by omega
    exact (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
      (D.minimum_le hi') (D.tail_cap R hm hkm ht hi' (by omega))).trans (D.lower _ hi')
  have hs := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hb := D.block_budget hkm
  by_cases h : charge A (D.r (m - 1)) ≤ charge A 0.42
  · rw [min_eq_left h] at hs
    exact hs.trans hb
  · rw [min_eq_right (le_of_not_ge h)] at hs
    linarith [R.cap_charge]

theorem minimum_le_root {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    D.r (m - 1) ≤ smallRoot A k := by
  have hb := D.minimum_charge_bound R hm hkm ht
  have hcap := D.tail_cap R hm hkm ht (by omega : m - 1 < m) (by omega : 3 ≤ m - 1)
  have hd : 0 ≤ A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  by_contra! h
  have hslope : 0 < 0.415 - (A - 0.15) * (D.r (m - 1) + smallRoot A k) := by
    have hmul := mul_le_mul_of_nonneg_left hcap hd
    linarith [R.root_slope]
  have hprod := mul_pos (sub_pos.mpr h) hslope
  have hcharge : charge A (smallRoot A k) < charge A (D.r (m - 1)) := by
    dsimp [charge]
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hcharge hk
  linarith [R.root_eq]

theorem tail_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    charge A (D.r (m - 1)) ≤ D.δ i := by
  have hbudget := D.minimum_charge_bound R hm hkm ht
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  have hcharge : charge A (D.r (m - 1)) ≤ charge A 0.42 := by
    have h := (lt_of_le_of_lt hbudget R.cap_charge)
    nlinarith
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (D.minimum_le hi) (D.tail_cap R hm hkm ht hi hi3)
  rw [min_eq_left hcharge] at h
  exact h.trans (D.lower i hi)

theorem third_large {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : 2.6 * D.r (m - 1) < D.r 2 ^ 2 := by
  let t := D.r (m - 1)
  let t₀ := smallRoot A k
  have ht0 : 0 < t := by dsimp [t]; linarith
  have htroot : t ≤ t₀ := D.minimum_le_root R hm hkm ht
  have htrootpos : 0 < t₀ := by dsimp [t₀]; linarith [R.root_lower]
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htlt : t₀ < 0.12 := R.root_upper
  have he_inc : charge A 0.066 ≤ charge A t := by
    have hmul := mul_le_mul_of_nonneg_left (show 0.066 + t ≤ 0.42 + t₀ by linarith) hd.le
    have hslope : 0 ≤ 0.415 - (A - 0.15) * (t + 0.066) := by
      linarith [R.root_slope]
    have hprod := mul_nonneg (show 0 ≤ t - 0.066 by dsimp [t]; linarith) hslope
    dsimp [charge]
    nlinarith
  have hfst : 1 - A < charge A 0.23 + (k : ℝ) * charge A t := by
    have hm := mul_le_mul_of_nonneg_left he_inc hk
    linarith [R.third_margin]
  have hspos : 0 < threshold A := div_pos (by norm_num) hd
  have hslopeeq : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hsqrtpos : 0 < Real.sqrt (2.6 * t₀) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtsq := Real.sq_sqrt (show 0 ≤ 2.6 * t₀ by positivity)
  have hsqrtlt : Real.sqrt (2.6 * t₀) < threshold A := by
    have hcap := R.root_cap
    dsimp [t₀] at hsqrtsq ⊢
    nlinarith
  have hepos : 0 < charge A (Real.sqrt (2.6 * t₀)) := by
    have hp := mul_pos hd (sub_pos.mpr hsqrtlt)
    have hp' := mul_pos hsqrtpos hp
    dsimp [charge]
    nlinarith
  have hend : 1 - A < finalBudget A k t₀ := by
    dsimp [finalBudget]
    linarith [R.root_eq]
  have hlower := (finalBudget_concave (by linarith [R.A_lower] : 0.15 ≤ A) hk).min_le_of_mem_Icc (by norm_num : (0.066 : ℝ) ∈ Set.Ici 0)
      (show t₀ ∈ Set.Ici 0 by exact htrootpos.le) (show t ∈ Set.Icc 0.066 t₀ by exact ⟨ht.le, htroot⟩)
  have hsnd : 1 - A < finalBudget A k t :=
    lt_of_lt_of_le (lt_min R.final_margin hend) hlower
  by_contra! hthird
  have hthirdpos := D.pos 2 (by omega)
  have hthirdlow := third_radius_gt hthirdpos (D.first_two_cap (by omega))
    (D.common_charge (by omega) R.A_lower)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
  have hthirdhi : D.r 2 ≤ Real.sqrt (2.6 * t) := by
    nlinarith [Real.sqrt_nonneg (2.6 * t)]
  have hthirdcharge := (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    hthirdlow.le hthirdhi).trans (D.lower 2 (by omega))
  have htailterm : ∀ i < k, charge A t ≤ D.δ (3 + i) := by
    intro i hi
    exact D.tail_charge R hm hkm ht (by omega) (by omega)
  have htail := Finset.sum_le_sum (fun i hi => htailterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htail
  have hb := D.prefix_block_budget hkm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hb
  have h0 := D.nonneg 0 (by omega)
  have h1 := D.nonneg 1 (by omega)
  dsimp [finalBudget] at hsnd
  rcases le_total (charge A 0.23) (charge A (Real.sqrt (2.6 * t))) with h | h
  · rw [min_eq_left h] at hthirdcharge
    linarith
  · rw [min_eq_right h] at hthirdcharge
    linarith

theorem incompatible {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (hdet₁ : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (D.r 2 ^ 2 - D.r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) : False := by
  have ht := D.minimum_lower hm R.A_lower hdet₁
  have htroot := D.minimum_le_root R hm hkm ht
  have ht12 := lt_of_le_of_lt htroot R.root_upper
  exact final_contradiction (by linarith : 0 < D.r (m - 1)) ht12
    (D.third_large R hm hkm ht) hdet₂

end RadiusData

theorem scalar_incompatibility {m : ℕ} (hm : 5 ≤ m) (r P : ℕ → ℝ)
    (hpos : ∀ i < m, 0 < r i) (hordered : AntitoneOn r (Set.Iio m))
    (hcap : ∀ i < m, r i ≤ 2 / 3)
    (hnorm : ∑ i ∈ Finset.range m, r i ^ 2 = 1)
    (hprob : ∑ i ∈ Finset.range m, P i = 1)
    (hquad : ∀ i < m, (if m = 5 then (0.929 : ℝ) else 0.884) * r i ^ 2 ≤ P i)
    (hlin : ∀ i < m, 0.415 * r i + 0.15 * r i ^ 2 ≤ P i)
    (hdet₁ : (r 2 ^ 2 - r (m - 1) ^ 2) *
      (r 0 ^ 2 + r 1 ^ 2 - r 2 ^ 2 - 2 * r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (r 2 ^ 2 - r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2) : False := by
  let A : ℝ := if m = 5 then 0.929 else 0.884
  let D : RadiusData m A := {
    r := r
    δ := fun i => P i - A * r i ^ 2
    pos := hpos
    ordered := hordered
    cap := hcap
    norm := hnorm
    nonneg := fun i hi => sub_nonneg.mpr (hquad i hi)
    lower := by intro i hi; dsimp [charge]; linarith [hlin i hi]
    budget := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hprob, mul_one] }
  by_cases hm5 : m = 5
  · have hR : Regime A 2 := by simpa [A, hm5] using regime_five
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂
  · have hR : Regime A 3 := by simpa [A, hm5] using regime_six
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂

end Scalar

end GaussianPropeller

end OAI
