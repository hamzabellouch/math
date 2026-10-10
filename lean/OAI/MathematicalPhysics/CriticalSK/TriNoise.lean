import OAI.MathematicalPhysics.CriticalSK.BlockEnergy

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

def scaleLength (J j : ℕ) : ℕ := 2 ^ (J - j)

def scaleRoot (J j : ℕ) : ℝ := (2 : ℝ)^j / (2 : ℝ)^J

def scaleEnergy (J j : ℕ) : ℝ := scaleRoot J j ^ 2

lemma scaleLength_pos (J j : ℕ) : 0 < scaleLength J j := by
  unfold scaleLength
  positivity

lemma scaleRoot_pos (J j : ℕ) : 0 < scaleRoot J j := by
  unfold scaleRoot
  positivity

lemma scaleEnergy_pos (J j : ℕ) : 0 < scaleEnergy J j := sq_pos_of_pos (scaleRoot_pos J j)

lemma scale_length_root_eq_one {J j : ℕ} (hj : j ≤ J) :
    (scaleLength J j : ℝ) * scaleRoot J j = 1 := by
  unfold scaleLength scaleRoot
  push_cast
  rw [← mul_div_assoc, ← pow_add, Nat.sub_add_cancel hj, div_self (by positivity)]

lemma scale_last (J : ℕ) : scaleRoot J (J + 1) = 2 := by
  unfold scaleRoot
  rw [pow_succ]
  field_simp

lemma scale_length_root {J j : ℕ} (hj : j ≤ J + 1) :
    1 ≤ (scaleLength J j : ℝ) * scaleRoot J j ∧
    (scaleLength J j : ℝ) * scaleRoot J j ≤ 2 := by
  by_cases h : j ≤ J
  · rw [scale_length_root_eq_one h]
    norm_num
  · have : j = J + 1 := by omega
    subst j
    simp [scaleLength, scale_last]

lemma scaleEnergy_step (J j : ℕ) : scaleEnergy J (j + 1) = 4 * scaleEnergy J j := by
  unfold scaleEnergy scaleRoot
  rw [pow_succ]
  ring

lemma energy_first_scale (J : ℕ) {e : ℝ} (hen : 0 ≤ e) (he : e ≤ 4) :
    ∃ j ≤ J + 1, e ≤ scaleEnergy J j ∧
      scaleEnergy J j ≤ 4 * (e + scaleEnergy J 0) := by
  by_cases he0 : e ≤ scaleEnergy J 0
  · exact ⟨0, by omega, he0, by nlinarith [scaleEnergy_pos J 0]⟩
  · have hex : ∃ j, e ≤ scaleEnergy J j := ⟨J + 1, by norm_num [scaleEnergy, scale_last]; exact he⟩
    let j := Nat.find hex
    have hj : j ≤ J + 1 := Nat.find_min' hex (by norm_num [scaleEnergy, scale_last]; exact he)
    have hj0 : 0 < j := by
      by_contra! h
      have : j = 0 := Nat.eq_zero_of_le_zero h
      exact he0 (this ▸ Nat.find_spec hex)
    have hprev : scaleEnergy J (j - 1) < e := lt_of_not_ge (Nat.find_min hex (by omega))
    refine ⟨j, hj, Nat.find_spec hex, ?_⟩
    have heq : j - 1 + 1 = j := by omega
    rw [← heq, scaleEnergy_step]
    nlinarith [scaleEnergy_pos J 0]

lemma scale_shell_geometry {N J j : ℕ} (hN : (N : ℝ) ≤ ((2 : ℝ)^J) ^ 3)
    (hj : j ≤ J + 1) :
    (N : ℝ) * scaleEnergy J j ≤ (8 : ℝ)^j * scaleLength J j := by
  have hscale := (scale_length_root hj).1
  have hp : (8 : ℝ)^j = ((2 : ℝ)^j)^3 := by
    rw [← pow_mul, mul_comm j 3, pow_mul]
    norm_num
  have hm : 0 < (2 : ℝ)^J := by positivity
  have ht : 0 < (2 : ℝ)^j := by positivity
  unfold scaleRoot at hscale
  rw [← mul_div_assoc, le_div_iff₀ hm] at hscale
  unfold scaleEnergy scaleRoot
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hm), hp]
  have hmul := mul_le_mul_of_nonneg_right hN (sq_nonneg ((2 : ℝ)^j))
  have hmul2 := mul_le_mul_of_nonneg_right hscale
    (by positivity : 0 ≤ ((2 : ℝ)^j)^2 * ((2 : ℝ)^J)^2)
  nlinarith

lemma dyadic_cube_scale (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ∧
    ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ≤ 8 * N := by
  have he : ((2 : ℝ)^Nat.clog 8 N) ^ 3 = (8 : ℝ)^Nat.clog 8 N := by
    rw [← pow_mul, mul_comm (Nat.clog 8 N) 3, pow_mul]
    norm_num
  rw [he]
  constructor
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 8) N
  · by_cases hn : N = 1
    · subst N
      norm_num [Nat.clog_one_right]
    · have hn' : 1 < N := by omega
      have hi := Nat.pow_pred_clog_lt_self (by decide : 1 < 8) hn'
      have hj := Nat.clog_pos (by decide : 1 < 8) hn'
      have hid : Nat.clog 8 N = (Nat.clog 8 N).pred + 1 := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj).symm
      rw [hid, pow_succ]
      have hi' : (8 : ℝ)^(Nat.clog 8 N).pred < N := by exact_mod_cast hi
      linarith

lemma natural_le_exponential_quarter (j : ℕ) :
    (j + 1 : ℝ) ≤ 8 * ((2 : ℝ)^j) ^ (1 / 4 : ℝ) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  have he := Real.add_one_le_exp ((j : ℝ) * Real.log 2 * (1 / 4 : ℝ))
  have hj : (0 : ℝ) ≤ j := by positivity
  nlinarith

lemma block_scale_factor {d t e : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hdt : 1 ≤ d * t) (hdt2 : d * t ≤ 2) (he : 0 ≤ e) (het : e ≤ t^2) :
    Real.sqrt d * (1 / d + 13 * Real.sqrt e) ≤ 27 * Real.sqrt t := by
  have hsd := Real.sq_sqrt hd.le
  have hst := Real.sq_sqrt ht.le
  have hse := Real.sq_sqrt he
  have hsd0 := Real.sqrt_pos.mpr hd
  have hst0 := Real.sqrt_pos.mpr ht
  have hsmall : Real.sqrt d / d ≤ Real.sqrt t := by
    apply (div_le_iff₀ hd).mpr
    have hmul := mul_le_mul_of_nonneg_right hdt hd.le
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [hsd, mul_pow, hst]
    nlinarith
  have hlarge : Real.sqrt d * Real.sqrt e ≤ 2 * Real.sqrt t := by
    have hm := mul_le_mul_of_nonneg_left het hd.le
    have hm2 := mul_le_mul_of_nonneg_right hdt2 ht.le
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hsd, hse, hst]
    nlinarith
  calc
    _ = Real.sqrt d / d + 13 * (Real.sqrt d * Real.sqrt e) := by ring
    _ ≤ Real.sqrt t + 13 * (2 * Real.sqrt t) := by linarith
    _ = _ := by ring

lemma scale_block_factor {J j : ℕ} (hj : j ≤ J + 1) {e : ℝ}
    (he : 0 ≤ e) (het : e ≤ scaleEnergy J j) :
    Real.sqrt (scaleLength J j) * (1 / scaleLength J j + 13 * Real.sqrt e) ≤
      27 * Real.sqrt (scaleRoot J j) :=
  block_scale_factor (by exact_mod_cast scaleLength_pos J j) (scaleRoot_pos J j)
    (scale_length_root hj).1 (scale_length_root hj).2 he het

lemma scale_weight_absorption (J j : ℕ) {e s h : ℝ} (hh : 0 ≤ h) (hes : 0 ≤ e + s)
    (hscale : scaleEnergy J j ≤ 4 * (e + s)) :
    (h + j + 1) * Real.sqrt (scaleRoot J j) ≤
      16 * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ) := by
  have hj : (0 : ℝ) ≤ j := by positivity
  have ht := scaleRoot_pos J j
  have hm : (0 : ℝ) < (2 : ℝ)^J := by positivity
  have hlin : h + j + 1 ≤ (h + 1) * (j + 1) := by nlinarith
  have hcoef := natural_le_exponential_quarter j
  have hfactor : ((2 : ℝ)^j) ^ (1 / 4 : ℝ) * Real.sqrt (scaleRoot J j) =
      ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (scaleEnergy J j) ^ (3 / 8 : ℝ) := by
    have htdef : (2 : ℝ)^j = (2 : ℝ)^J * scaleRoot J j := by
      unfold scaleRoot
      field_simp
    rw [htdef, Real.mul_rpow hm.le ht.le, Real.sqrt_eq_rpow]
    unfold scaleEnergy
    rw [← Real.rpow_natCast (scaleRoot J j) 2, ← Real.rpow_mul ht.le,
      mul_assoc, ← Real.rpow_add ht]
    norm_num
  have hfour : (4 : ℝ) ^ (3 / 8 : ℝ) ≤ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2)
    simpa only [← Real.sqrt_eq_rpow, show Real.sqrt 4 = 2 by norm_num] using hp
  have henergy : (scaleEnergy J j) ^ (3 / 8 : ℝ) ≤ 2 * (e + s) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ (4 * (e + s)) ^ (3 / 8 : ℝ) := Real.rpow_le_rpow (scaleEnergy_pos J j).le hscale (by norm_num)
      _ = (4 : ℝ) ^ (3 / 8 : ℝ) * (e + s) ^ (3 / 8 : ℝ) := Real.mul_rpow (by norm_num) hes
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hes _)
  calc
    _ ≤ ((h + 1) * (j + 1)) * Real.sqrt (scaleRoot J j) :=
      mul_le_mul_of_nonneg_right hlin (Real.sqrt_nonneg _)
    _ ≤ ((h + 1) * (8 * ((2 : ℝ)^j) ^ (1 / 4 : ℝ))) * Real.sqrt (scaleRoot J j) := by
      gcongr
    _ = 8 * (h + 1) * (((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (scaleEnergy J j) ^ (3 / 8 : ℝ)) := by
      rw [← hfactor]
      ring
    _ ≤ 8 * (h + 1) * (((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (2 * (e + s) ^ (3 / 8 : ℝ))) := by
      gcongr
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma good_scale_prefix {X : ℕ → Ω → ℝ} {c : ℝ≥0} {J N : ℕ} {h : ℝ} {ω : Ω}
    (hh : 0 ≤ h)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength J j - 1) (J + 2) N h)
    {j r b k : ℕ} (hj : j ≤ J + 1) (hr : r < N) (hb : b ∈ blockShell j r)
    (hk : k < scaleLength J j) :
    |∑ i ∈ Finset.range (k + 1), X (b * scaleLength J j + i) ω| ≤
      (Real.sqrt (32 * (c : ℝ)) * Real.sqrt (scaleLength J j)) * (h + j + r + 1) := by
  have hd := scaleLength_pos J j
  have he : scaleLength J j - 1 + 1 = scaleLength J j := by omega
  have hp := good_multiscale_prefix_all hω (j := j) (r := r) (b := b)
    (by omega) (by omega) hb (k := k) (by omega)
  simpa only [he] using hp.trans (blockThreshold_length_bound c (scaleLength J j) j r hd hh)

lemma selected_scale_form_bound {J j : ℕ} {e s h c a : ℝ}
    (hj : j ≤ J + 1) (he : 0 ≤ e) (hs : 0 ≤ s) (hh : 0 ≤ h) (_hc : 0 ≤ c)
    (heσ : e ≤ scaleEnergy J j) (hσ : scaleEnergy J j ≤ 4 * (e + s))
    (ha : a ≤ 32 * (Real.sqrt (32 * c) * Real.sqrt (scaleLength J j)) *
      (h + j + 1) * (1 / scaleLength J j + 13 * Real.sqrt e)) :
    a ≤ 13824 * Real.sqrt (32 * c) * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) *
      (e + s) ^ (3 / 8 : ℝ) := by
  calc
    a ≤ 32 * Real.sqrt (32 * c) * (h + j + 1) *
        (Real.sqrt (scaleLength J j) * (1 / scaleLength J j + 13 * Real.sqrt e)) := by
      convert ha using 1
      ring
    _ ≤ 32 * Real.sqrt (32 * c) * (h + j + 1) * (27 * Real.sqrt (scaleRoot J j)) :=
      mul_le_mul_of_nonneg_left (scale_block_factor hj he heσ) (by positivity)
    _ = 864 * Real.sqrt (32 * c) * ((h + j + 1) * Real.sqrt (scaleRoot J j)) := by ring
    _ ≤ 864 * Real.sqrt (32 * c) *
        (16 * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (scale_weight_absorption J j hh (add_nonneg he hs) hσ) (by positivity)
    _ = _ := by ring

omit [MeasurableSpace Ω] in
lemma centered_square_form_good {X : ℕ → Ω → ℝ} {c : ℝ≥0} (n : ℕ) {h s : ℝ} {ω : Ω}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
      (Nat.clog 8 (n + 1) + 2) (n + 1) h)
    (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i^2) = 1) :
    |∑ i ∈ Finset.range (n + 1), X i ω * u i^2| ≤
      13824 * Real.sqrt (32 * (c : ℝ)) * (h + 1) *
        ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) *
        (pathEnergy n u + s) ^ (3 / 8 : ℝ) := by
  have he0 := pathEnergy_nonneg n u
  have he4 : pathEnergy n u ≤ 4 := by simpa only [hnorm, mul_one] using pathEnergy_le_four_mass n u
  obtain ⟨j, hj, heσ, hσ⟩ := energy_first_scale (Nat.clog 8 (n + 1)) he0 he4
  have hsize := scale_shell_geometry (dyadic_cube_scale (n + 1) (by omega)).1 hj
  have hscale := square_multiscale_prefix (fun i => X i ω) n j
    (scaleLength (Nat.clog 8 (n + 1)) j) (scaleLength_pos _ _) u hu hnorm
    (scaleEnergy_pos _ _) hh (by positivity) heσ (by exact_mod_cast hsize)
    (fun r hr b _ hb k hk => good_scale_prefix hh hω hj hr hb hk)
  exact selected_scale_form_bound hj he0 ((scaleEnergy_pos _ _).le.trans hs) hh c.prop
    heσ (hσ.trans (by linarith)) hscale

omit [MeasurableSpace Ω] in
lemma centered_product_form_good {X : ℕ → Ω → ℝ} {c : ℝ≥0} (n : ℕ) {h s : ℝ} {ω : Ω}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
      (Nat.clog 8 (n + 1) + 2) (n + 1) h)
    (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i^2) = 1) :
    |∑ i ∈ Finset.range (n + 1), X i ω * (u i * u (i + 1))| ≤
      13824 * Real.sqrt (32 * (c : ℝ)) * (h + 1) *
        ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) *
        (pathEnergy n u + s) ^ (3 / 8 : ℝ) := by
  have he0 := pathEnergy_nonneg n u
  have he4 : pathEnergy n u ≤ 4 := by simpa only [hnorm, mul_one] using pathEnergy_le_four_mass n u
  obtain ⟨j, hj, heσ, hσ⟩ := energy_first_scale (Nat.clog 8 (n + 1)) he0 he4
  have hsize := scale_shell_geometry (dyadic_cube_scale (n + 1) (by omega)).1 hj
  have hscale := product_multiscale_prefix (fun i => X i ω) n j
    (scaleLength (Nat.clog 8 (n + 1)) j) (scaleLength_pos _ _) u hu hnorm
    (scaleEnergy_pos _ _) hh (by positivity) heσ (by exact_mod_cast hsize)
    (fun r hr b _ hb k hk => good_scale_prefix hh hω hj hr hb hk)
  exact selected_scale_form_bound hj he0 ((scaleEnergy_pos _ _).le.trans hs) hh c.prop
    heσ (hσ.trans (by linarith)) hscale

end

lemma edgeCoeff_sqrt_div (n i : ℕ) (hi : i ≤ n) :
    edgeCoeff n i = Real.sqrt (n - i : ℕ) / Real.sqrt (n + 1 : ℝ) := by
  rw [edgeCoeff, ← Real.sqrt_div (by positivity)]
  congr 1
  rw [Nat.cast_sub hi]
  field_simp
  ring

lemma chi_scaled_bias_bound (n i : ℕ) (hi : i < n) :
    (Real.sqrt (n - i : ℕ) - ∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) /
      Real.sqrt (n + 1 : ℝ) ≤
      4 / (n + 1) + (4 / Real.sqrt (n + 1 : ℝ)) * ((i + 1 : ℝ) / (n + 1)) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hsN : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hN
  have hm : 0 < n - i := by omega
  have hsm : 0 < Real.sqrt (n - i : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hb := (chi_mean_bias (n - i) hm).2
  have hb2 := chi_bias_le_two (n - i) hm
  by_cases hearly : 2 * (i + 1 : ℝ) ≤ n + 1
  · have hdiff : (n + 1 : ℝ) / 2 ≤ (n - i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      linarith
    have hroot : Real.sqrt (n + 1 : ℝ) ≤ 2 * Real.sqrt (n - i : ℕ) := by
      have hsqN := Real.sq_sqrt hN.le
      have hd0 : (0 : ℝ) ≤ (n - i : ℕ) := Nat.cast_nonneg _
      have hsqD := Real.sq_sqrt hd0
      nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n - i : ℕ)]
    have hbound : (Real.sqrt (n - i : ℕ) - ∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) /
        Real.sqrt (n + 1 : ℝ) ≤ 4 / (n + 1) := by
      apply (div_le_iff₀ hsN).mpr
      have hprod : 2 / Real.sqrt (n - i : ℕ) ≤ 4 / Real.sqrt (n + 1 : ℝ) := by
        apply (div_le_div_iff₀ hsm hsN).mpr
        linarith
      have hid : 4 / (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) = 4 / Real.sqrt (n + 1 : ℝ) := by
        have hsq := Real.sq_sqrt hN.le
        field_simp
        nlinarith
      rw [hid]
      exact hb.trans hprod
    exact hbound.trans (le_add_of_nonneg_right (by positivity))
  · have hlate : (1 / 2 : ℝ) ≤ (i + 1 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hN).mpr
      push Not at hearly
      linarith
    calc
      _ ≤ 2 / Real.sqrt (n + 1 : ℝ) := div_le_div_of_nonneg_right hb2 hsN.le
      _ ≤ (4 / Real.sqrt (n + 1 : ℝ)) * ((i + 1 : ℝ) / (n + 1)) := by
        have := mul_le_mul_of_nonneg_left hlate (show 0 ≤ 4 / Real.sqrt (n + 1 : ℝ) by positivity)
        calc
          2 / Real.sqrt (n + 1 : ℝ) = (4 / Real.sqrt (n + 1 : ℝ)) * (1 / 2) := by ring
          _ ≤ _ := this
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma weighted_neighbor_sum (n : ℕ) (u w : ℕ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ w (i + 1)) :
    (∑ i ∈ Finset.range n, w i * (u i ^ 2 + u (i + 1) ^ 2)) ≤
      2 * ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
  have ha : (∑ i ∈ Finset.range n, w i * u i ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (mul_nonneg (hw0 _) (sq_nonneg _))
  have hb : (∑ i ∈ Finset.range n, w i * u (i + 1) ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, w (i + 1) * u (i + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
      _ ≤ _ := by
        rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (mul_nonneg (hw0 _) (sq_nonneg _))
  simp_rw [mul_add, Finset.sum_add_distrib]
  linarith

lemma weighted_edge_form (n : ℕ) (u a : ℕ → ℝ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ∀ i < n, |a i| ≤ B + C * ((i + 1 : ℝ) / (n + 1))) :
    2 * |∑ i ∈ Finset.range n, a i * u i * u (i + 1)| ≤
      2 * B * (∑ i ∈ Finset.range (n + 1), u i ^ 2) + 4 * C * pathEnergy n u := by
  let w (i : ℕ) : ℝ := B + C * ((i + 1 : ℝ) / (n + 1))
  have hw0 : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hw : ∀ i, w i ≤ w (i + 1) := by
    intro i
    dsimp [w]
    gcongr
    norm_num
  have habs : 2 * |∑ i ∈ Finset.range n, a i * u i * u (i + 1)| ≤
      ∑ i ∈ Finset.range n, w i * (u i ^ 2 + u (i + 1) ^ 2) := by
    calc
      _ ≤ 2 * ∑ i ∈ Finset.range n, |a i * u i * u (i + 1)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ = ∑ i ∈ Finset.range n, |a i| * (2 * |u i * u (i + 1)|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [abs_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul (ha i (Finset.mem_range.mp hi)) ?_ (by positivity) (hw0 i)
        nlinarith [sq_nonneg (|u i| - |u (i + 1)|), sq_abs (u i), sq_abs (u (i + 1)),
          show |u i * u (i + 1)| = |u i| * |u (i + 1)| from abs_mul _ _]
  have hid : (∑ i ∈ Finset.range (n + 1), w i * u i ^ 2) =
      B * (∑ i ∈ Finset.range (n + 1), u i ^ 2) +
        C * (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) := by
    simp only [w, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  have hvari := pathEnergy_weighted_mass n u
  have hn := habs.trans (weighted_neighbor_sum n u w hw0 hw)
  rw [hid] at hn
  nlinarith [mul_le_mul_of_nonneg_left hvari hC]

lemma chi_mean_form_bias (n : ℕ) (u : ℕ → ℝ) :
    2 * |∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)| ≤
      8 / (n + 1) * (∑ i ∈ Finset.range (n + 1), u i ^ 2) +
        16 / Real.sqrt (n + 1 : ℝ) * pathEnergy n u := by
  have hb := weighted_edge_form n u
    (fun i => (∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ) -
      edgeCoeff n i)
    (B := 4 / (n + 1)) (C := 4 / Real.sqrt (n + 1 : ℝ)) (by positivity) (by positivity) ?_
  · convert hb using 1
    ring
  intro i hi
  rw [edgeCoeff_sqrt_div n i (by omega), ← sub_div]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm,
    abs_of_nonneg (chi_mean_bias (n - i) (by omega)).1]
  exact chi_scaled_bias_bound n i hi

def entryVariance (n : ℕ) : ℝ≥0 := ⟨2 * (48 * Real.exp 1 + 4) / (n + 1), by positivity⟩

lemma entryVariance_pos (n : ℕ) : 0 < entryVariance n := by
  change 0 < 2 * (48 * Real.exp 1 + 4) / (n + 1 : ℝ)
  positivity

lemma subGaussian_enlarge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  gcongr

lemma diagonalRows_common_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω i) (entryVariance n) (diagonalLaw n) := by
  apply subGaussian_enlarge (diagonalRows_subGaussian n i)
  change 2 / (n + 1 : ℝ) ≤ 2 * (48 * Real.exp 1 + 4) / (n + 1)
  gcongr
  have := Real.exp_pos (1 : ℝ)
  linarith

abbrev TriSample (n : ℕ) := (ℕ → ℝ) × ChiRows n

def triLaw (n : ℕ) : Measure (TriSample n) := (diagonalLaw n).prod (chiRowLaw n)

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

def entryBad {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (h : ℝ) : Set Ω :=
  multiscaleBad X (entryVariance n) (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
    (Nat.clog 8 (n + 1) + 2) (n + 1) h

def triBad (n : ℕ) (h : ℝ) : Set (TriSample n) :=
  Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h ∪
    Prod.snd ⁻¹' entryBad n (scaledChiRow n) h

lemma entryBad_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h : ℝ) : MeasurableSet (entryBad n X h) :=
  multiscaleBad_measurable X hX _ _ _ _ _

lemma triBad_measurable (n : ℕ) (h : ℝ) : MeasurableSet (triBad n h) :=
  ((entryBad_measurable n _ (fun i => measurable_pi_apply i) h).preimage measurable_fst).union
    ((entryBad_measurable n _ (scaledChiRow_measurable n) h).preimage measurable_snd)

lemma triBad_probability (n : ℕ) (h : ℝ) :
    (triLaw n).real (triBad n h) ≤ 32 * Real.exp (-h ^ 2) := by
  have ha : (diagonalLaw n).real (entryBad n (fun i (ω : ℕ → ℝ) => ω i) h) ≤
      16 * Real.exp (-h ^ 2) :=
    multiscaleBad_probability (fun i => (measurable_pi_apply i).stronglyMeasurable)
      (diagonalRows_independent n) (diagonalRows_common_subGaussian n) (diagonalRows_mean n)
      (entryVariance_pos n) _ _ _ _
  have hb : (chiRowLaw n).real (entryBad n (scaledChiRow n) h) ≤
      16 * Real.exp (-h ^ 2) :=
    multiscaleBad_probability (fun i => (scaledChiRow_measurable n i).stronglyMeasurable)
      (scaledChiRows_independent n) (scaledChiRow_subGaussian n) (scaledChiRow_mean n)
      (entryVariance_pos n) _ _ _ _
  have hU := measureReal_union_le (μ := triLaw n)
    (Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h)
    (Prod.snd ⁻¹' entryBad n (scaledChiRow n) h)
  have heA : Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h =
      (entryBad n (fun i (ω : ℕ → ℝ) => ω i) h) ×ˢ (Set.univ : Set (ChiRows n)) := by ext; simp
  have heB : Prod.snd ⁻¹' entryBad n (scaledChiRow n) h =
      (Set.univ : Set (ℕ → ℝ)) ×ˢ (entryBad n (scaledChiRow n) h) := by ext; simp
  simpa only [triBad, heA, heB, triLaw, measureReal_prod_prod, probReal_univ, mul_one, one_mul]
    using hU.trans (by simpa only [heA, heB, triLaw, measureReal_prod_prod, probReal_univ,
      mul_one, one_mul] using (show _ + _ ≤ 32 * Real.exp (-h ^ 2) by linarith [ha, hb]))

def triForm (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * ∑ i ∈ Finset.range n,
      (chi (chiRowDim n i) (ω.2 i) / Real.sqrt (n + 1 : ℝ)) * u i * u (i + 1)

lemma triForm_decomposition (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) :
    triForm n ω u - (2 * (∑ i ∈ Finset.range (n + 1), u i ^ 2) - pathEnergy n u) =
    (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))) +
    2 * (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)) := by
  unfold triForm pathEnergy
  have he : (∑ i ∈ Finset.range n,
      (chi (chiRowDim n i) (ω.2 i) / Real.sqrt (n + 1 : ℝ)) * u i * u (i + 1)) =
      (∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)) +
      (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))) +
      (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hd : chiRowDim n i = n - i := by unfold chiRowDim; have := Finset.mem_range.mp hi; omega
    have hmean : (∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)) =
        (∫ y, chi (n - i) y ∂standardGaussianProduct (n - i)) := by rw [hd]
    simp only [scaledChiRow, centeredChiRow]
    rw [hmean]
    ring
  rw [he]
  ring

def formError (n : ℕ) (h s e : ℝ) : ℝ :=
  41472 * Real.sqrt (32 * (entryVariance n : ℝ)) * (h + 1) *
    ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ) +
    8 / (n + 1) + 16 / Real.sqrt (n + 1 : ℝ) * e

lemma triForm_good (n : ℕ) {h s : ℝ} {ω : TriSample n}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ triBad n h) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1) :
    |triForm n ω u - (2 - pathEnergy n u)| ≤ formError n h s (pathEnergy n u) := by
  have hA : ω.1 ∉ entryBad n (fun i (a : ℕ → ℝ) => a i) h := by
    intro ha
    exact hω (Or.inl ha)
  have hB : ω.2 ∉ entryBad n (scaledChiRow n) h := by
    intro hb
    exact hω (Or.inr hb)
  have ha := centered_square_form_good n hh hs hA u hu hnorm
  have hb := centered_product_form_good n hh hs hB u hu hnorm
  have hbias := chi_mean_form_bias n u
  rw [hnorm, mul_one] at hbias
  have heB : (∑ i ∈ Finset.range (n + 1), scaledChiRow n i ω.2 * (u i * u (i + 1))) =
      ∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1)) := by
    rw [Finset.sum_range_succ, hu (n + 1) (by omega)]
    ring
  rw [heB] at hb
  have he := triForm_decomposition n ω u
  rw [hnorm, mul_one] at he
  rw [he]
  have habs := abs_add_le
    ((∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))))
    (2 * (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)))
  have habs2 := abs_add_le
    (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2)
    (2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))))
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs habs2
  dsimp only [formError]
  linarith

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (triLaw n) := by
  unfold triLaw
  infer_instance

end CriticalSK

end

end OAI
