import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.FiniteNoise
import OAI.InformationTheory.SoftChannel.Model

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

def bose (z : ℝ) : ℝ := (Real.exp z - 1)⁻¹

def canonicalQ (z : ℝ) : ℝ := z * bose z - Real.log (1 - Real.exp (-z))

def normalizedEntropy (z w : ℝ) : ℝ :=
  let u := bose z
  let v := bose w
  let n := 1 + u + v
  n * Real.log n - ((u + 1) * Real.log (u + 1) + u * Real.log u +
    (v + 1) * Real.log (v + 1) + v * Real.log v) / 2

lemma bose_pos {z : ℝ} (hz : 0 < z) : 0 < bose z := by
  exact inv_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz))

lemma exp_neg_lt_one {z : ℝ} (hz : 0 < z) : Real.exp (-z) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr hz)

lemma bose_eq_exp_neg {z : ℝ} (hz : 0 < z) :
    bose z = Real.exp (-z) / (1 - Real.exp (-z)) := by
  have he := (Real.one_lt_exp_iff.mpr hz : 1 < Real.exp z)
  rw [Real.exp_neg]
  unfold bose
  field_simp

lemma hasDerivAt_bose {z : ℝ} (hz : 0 < z) :
    HasDerivAt bose (-(bose z * (bose z + 1))) z := by
  have he : Real.exp z - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz))
  convert! (((Real.hasDerivAt_exp z).sub_const 1).inv he) using 1
  unfold bose
  field_simp
  ring

lemma hasDerivAt_canonicalQ {z : ℝ} (hz : 0 < z) :
    HasDerivAt canonicalQ (-z * bose z * (bose z + 1)) z := by
  have hneg : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-z)) z := by
    convert! (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg using 1; ring
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_bose hz)).sub
    ((hneg.const_sub 1).log (ne_of_gt (sub_pos.mpr (exp_neg_lt_one hz))))
  convert! hd using 1
  simp only [id_eq, neg_neg]
  rw [bose_eq_exp_neg hz]
  ring

lemma hasDerivAt_canonicalQ_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => -t * bose t * (bose t + 1))
      (bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1)) z := by
  convert! (((hasDerivAt_id z).neg.mul (hasDerivAt_bose hz)).mul
    ((hasDerivAt_bose hz).add_const 1)) using 1
  simp only [Pi.mul_apply, Pi.neg_apply, id_eq]
  ring

lemma canonicalQ_second_pos {z : ℝ} (hz : 0 < z) :
    0 < bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1) := by
  have hb := bose_pos hz
  apply mul_pos (mul_pos hb (by linarith))
  have hexp : 1 - z < Real.exp (-z) := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr hz.ne')
    linarith
  have he : 0 < 1 - Real.exp (-z) := sub_pos.mpr (exp_neg_lt_one hz)
  rw [bose_eq_exp_neg hz]
  rw [show z * (2 * (Real.exp (-z) / (1 - Real.exp (-z))) + 1) - 1 =
    (z * (1 + Real.exp (-z)) - (1 - Real.exp (-z))) / (1 - Real.exp (-z)) by
      field_simp; ring]
  apply div_pos _ he
  nlinarith [Real.exp_pos (-z)]

lemma convexOn_canonicalQ : ConvexOn ℝ (Ioi 0) canonicalQ := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun z hz => (hasDerivAt_canonicalQ hz).continuousAt.continuousWithinAt)
    (f' := fun z => -z * bose z * (bose z + 1))
    (f'' := fun z => bose z * (bose z + 1) * (z * (2 * bose z + 1) - 1))
  · intro z hz
    exact (hasDerivAt_canonicalQ (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (hasDerivAt_canonicalQ_deriv (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (canonicalQ_second_pos (by simpa using hz)).le

def canonicalGroup (z w : ℝ) (n : ℕ) : ℝ :=
  ((∑ j ∈ Finset.range (n + 1), Real.exp (-((n + 1 : ℕ) * z + (j + 1 : ℕ) * w))) +
    ∑ i ∈ Finset.range n, Real.exp (-((i + 1 : ℕ) * z + (n + 1 : ℕ) * w))) /
    (n + 1 : ℕ)

lemma exp_pair (z w : ℝ) (i j : ℕ) :
    Real.exp (-((i : ℝ) * z + (j : ℝ) * w)) =
      Real.exp (-z) ^ i * Real.exp (-w) ^ j := by
  rw [show -((i : ℝ) * z + (j : ℝ) * w) = (i : ℝ) * (-z) + (j : ℝ) * (-w) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]

lemma geom_positive_sum {x : ℝ} (hx : x ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ (i + 1) = x / (1 - x) * (1 - x ^ n) := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq hx]
  field_simp
  ring

lemma canonicalGroup_eq {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (k : ℕ) :
    canonicalGroup z w k =
      bose w * (Real.exp (-z) ^ (k + 1) / (k + 1 : ℕ)) +
      bose z * (Real.exp (-w) ^ (k + 1) / (k + 1 : ℕ)) -
      (1 + bose z + bose w) * ((Real.exp (-z) * Real.exp (-w)) ^ (k + 1) /
        (k + 1 : ℕ)) := by
  have hz1 := (exp_neg_lt_one hz).ne
  have hw1 := (exp_neg_lt_one hw).ne
  unfold canonicalGroup
  simp_rw [exp_pair, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [geom_positive_sum hw1, geom_positive_sum hz1,
    bose_eq_exp_neg hz, bose_eq_exp_neg hw]
  simp only [mul_pow, pow_succ]
  field_simp
  ring

lemma hasSum_canonicalGroup {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    HasSum (canonicalGroup z w)
      ((1 + bose z + bose w) * Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        bose w * Real.log (1 - Real.exp (-z)) -
        bose z * Real.log (1 - Real.exp (-w))) := by
  have hx : |Real.exp (-z)| < 1 := by rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one hz
  have hy : |Real.exp (-w)| < 1 := by rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one hw
  have hxy : |Real.exp (-z) * Real.exp (-w)| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Real.exp (-z)), abs_nonneg (Real.exp (-w))]
  convert! (((Real.hasSum_pow_div_log_of_abs_lt_one hx).mul_left (bose w)).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left (bose z))).sub
    ((Real.hasSum_pow_div_log_of_abs_lt_one hxy).mul_left (1 + bose z + bose w)) using 1
  · ext k
    simpa only [Nat.cast_add, Nat.cast_one] using canonicalGroup_eq hz hw k
  · ring

lemma log_bose {z : ℝ} (hz : 0 < z) :
    Real.log (bose z) = -z - Real.log (1 - Real.exp (-z)) := by
  rw [bose_eq_exp_neg hz, Real.log_div (Real.exp_ne_zero _)
    (ne_of_gt (sub_pos.mpr (exp_neg_lt_one hz))), Real.log_exp]

lemma log_bose_add_one {z : ℝ} (hz : 0 < z) :
    Real.log (bose z + 1) = -Real.log (1 - Real.exp (-z)) := by
  rw [bose_eq_exp_neg hz]
  have he := (sub_pos.mpr (exp_neg_lt_one hz)).ne'
  rw [show Real.exp (-z) / (1 - Real.exp (-z)) + 1 =
    (1 - Real.exp (-z))⁻¹ by field_simp; ring, Real.log_inv]

lemma log_one_add_bose_add_bose {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    Real.log (1 + bose z + bose w) =
      Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        Real.log (1 - Real.exp (-z)) - Real.log (1 - Real.exp (-w)) := by
  have hx := (sub_pos.mpr (exp_neg_lt_one hz)).ne'
  have hy := (sub_pos.mpr (exp_neg_lt_one hw)).ne'
  have hxy : 0 < 1 - Real.exp (-z) * Real.exp (-w) := by
    have hz1 := exp_neg_lt_one hz
    have hw1 := exp_neg_lt_one hw
    nlinarith [Real.exp_pos (-z), Real.exp_pos (-w)]
  rw [bose_eq_exp_neg hz, bose_eq_exp_neg hw]
  rw [show 1 + Real.exp (-z) / (1 - Real.exp (-z)) +
    Real.exp (-w) / (1 - Real.exp (-w)) =
    (1 - Real.exp (-z) * Real.exp (-w)) / ((1 - Real.exp (-z)) * (1 - Real.exp (-w))) by
      field_simp; ring]
  rw [Real.log_div hxy.ne' (mul_ne_zero hx hy), Real.log_mul hx hy]
  ring

lemma normalizedEntropy_series_identity {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    normalizedEntropy z w = (canonicalQ z + canonicalQ w) / 2 +
      ((1 + bose z + bose w) * Real.log (1 - Real.exp (-z) * Real.exp (-w)) -
        bose w * Real.log (1 - Real.exp (-z)) -
        bose z * Real.log (1 - Real.exp (-w))) := by
  unfold normalizedEntropy canonicalQ
  dsimp only
  rw [log_bose hz, log_bose hw, log_bose_add_one hz, log_bose_add_one hw,
    log_one_add_bose_add_bose hz hw]
  ring

lemma hasSum_normalizedEntropy {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    HasSum (canonicalGroup z w)
      (normalizedEntropy z w - (canonicalQ z + canonicalQ w) / 2) := by
  rw [normalizedEntropy_series_identity hz hw]
  convert! hasSum_canonicalGroup hz hw using 1; ring

lemma canonicalExp_jensen (z₁ w₁ z₂ w₂ i j : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.exp (-(i * (a * z₁ + b * z₂) + j * (a * w₁ + b * w₂))) ≤
      a * Real.exp (-(i * z₁ + j * w₁)) + b * Real.exp (-(i * z₂ + j * w₂)) := by
  convert! convexOn_exp.2 (mem_univ (-(i*z₁+j*w₁)))
    (mem_univ (-(i*z₂+j*w₂))) ha hb hab using 1;
    simp only [smul_eq_mul]; congr 1; ring

lemma canonicalGroup_jensen (z₁ w₁ z₂ w₂ : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (n : ℕ) :
    canonicalGroup (a*z₁+b*z₂) (a*w₁+b*w₂) n ≤
      a * canonicalGroup z₁ w₁ n + b * canonicalGroup z₂ w₂ n := by
  unfold canonicalGroup
  have h₁ := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j _ =>
    canonicalExp_jensen z₁ w₁ z₂ w₂ (n+1 : ℕ) (j+1 : ℕ) ha hb hab)
  have h₂ := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    canonicalExp_jensen z₁ w₁ z₂ w₂ (i+1 : ℕ) (n+1 : ℕ) ha hb hab)
  have h := div_le_div_of_nonneg_right (add_le_add h₁ h₂)
    (show (0 : ℝ) ≤ (n+1 : ℕ) by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  convert! h using 1; ring

lemma normalizedEntropy_jensen {z₁ w₁ z₂ w₂ a b : ℝ}
    (hz₁ : 0 < z₁) (hw₁ : 0 < w₁) (hz₂ : 0 < z₂) (hw₂ : 0 < w₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    normalizedEntropy (a*z₁+b*z₂) (a*w₁+b*w₂) ≤
      a * normalizedEntropy z₁ w₁ + b * normalizedEntropy z₂ w₂ := by
  have hz : 0 < a*z₁+b*z₂ := by
    simpa only [mem_Ioi, smul_eq_mul] using (convex_Ioi (0 : ℝ)) hz₁ hz₂ ha hb hab
  have hw : 0 < a*w₁+b*w₂ := by
    simpa only [mem_Ioi, smul_eq_mul] using (convex_Ioi (0 : ℝ)) hw₁ hw₂ ha hb hab
  have hseries := hasSum_le (canonicalGroup_jensen z₁ w₁ z₂ w₂ ha hb hab)
    (hasSum_normalizedEntropy hz hw)
    (((hasSum_normalizedEntropy hz₁ hw₁).mul_left a).add
      ((hasSum_normalizedEntropy hz₂ hw₂).mul_left b))
  have hqz := convexOn_canonicalQ.2 hz₁ hz₂ ha hb hab
  have hqw := convexOn_canonicalQ.2 hw₁ hw₂ ha hb hab
  simp only [smul_eq_mul] at hqz hqw
  linarith

def normalizedEntropyDz (z w : ℝ) : ℝ :=
  -bose z * (bose z + 1) * (Real.log (1 + bose z + bose w) -
    (Real.log (bose z + 1) + Real.log (bose z)) / 2)

lemma normalizedEntropy_symm (z w : ℝ) : normalizedEntropy z w = normalizedEntropy w z := by
  unfold normalizedEntropy
  dsimp only
  rw [show 1 + bose w + bose z = 1 + bose z + bose w by ring]
  ring

lemma normalizedEntropyDz_neg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    normalizedEntropyDz z w < 0 := by
  have hu := bose_pos hz
  have hv := bose_pos hw
  have h₁ := Real.log_lt_log (by linarith : 0 < bose z + 1)
    (show bose z + 1 < 1 + bose z + bose w by linarith)
  have h₂ := Real.log_lt_log hu (show bose z < 1 + bose z + bose w by linarith)
  unfold normalizedEntropyDz
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hu) (by linarith))
    (by linarith)

lemma hasDerivAt_normalizedEntropy_comp {z w : ℝ → ℝ} {t z' w' : ℝ}
    (hzD : HasDerivAt z z' t) (hwD : HasDerivAt w w' t)
    (hz : 0 < z t) (hw : 0 < w t) :
    HasDerivAt (fun s => normalizedEntropy (z s) (w s))
      (normalizedEntropyDz (z t) (w t) * z' + normalizedEntropyDz (w t) (z t) * w') t := by
  have hu := bose_pos hz
  have hv := bose_pos hw
  have huD := (hasDerivAt_bose hz).comp t hzD
  have hvD := (hasDerivAt_bose hw).comp t hwD
  have hnD := (huD.const_add 1).add hvD
  have h₁ := (Real.hasDerivAt_mul_log (by linarith : 1 + bose (z t) + bose (w t) ≠ 0)).comp t hnD
  have h₂ := (Real.hasDerivAt_mul_log (by linarith : bose (z t) + 1 ≠ 0)).comp t (huD.add_const 1)
  have h₃ := (Real.hasDerivAt_mul_log hu.ne').comp t huD
  have h₄ := (Real.hasDerivAt_mul_log (by linarith : bose (w t) + 1 ≠ 0)).comp t (hvD.add_const 1)
  have h₅ := (Real.hasDerivAt_mul_log hv.ne').comp t hvD
  convert! h₁.sub ((((h₂.add h₃).add h₄).add h₅).div_const 2) using 1
  unfold normalizedEntropyDz
  rw [show 1 + bose (w t) + bose (z t) = 1 + bose (z t) + bose (w t) by ring]
  ring

lemma positive_line {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : t ∈ Icc 0 1) :
    0 < x + t * (y - x) := by
  have h := (convex_Ioi (0 : ℝ)) hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  simp only [smul_eq_mul, mem_Ioi] at h
  nlinarith

lemma normalizedEntropy_tangent {z w Z W : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hZ : 0 < Z) (hW : 0 < W) :
    normalizedEntropy z w + normalizedEntropyDz z w * (Z-z) +
      normalizedEntropyDz w z * (W-w) ≤ normalizedEntropy Z W := by
  let f : ℝ → ℝ := fun t => normalizedEntropy (z+t*(Z-z)) (w+t*(W-w))
  have hc : ConvexOn ℝ (Icc 0 1) f := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := normalizedEntropy_jensen (positive_line hz hZ hx) (positive_line hw hW hx)
      (positive_line hz hZ hy) (positive_line hw hW hy) ha hb hab
    convert! h using 1; simp only [f, smul_eq_mul]
    congr 1 <;> nlinarith [congrArg (fun q : ℝ => q*z) hab, congrArg (fun q : ℝ => q*w) hab]
  have hd : HasDerivAt f (normalizedEntropyDz z w * (Z-z) +
      normalizedEntropyDz w z * (W-w)) 0 := by
    convert! hasDerivAt_normalizedEntropy_comp
      (((hasDerivAt_id (0 : ℝ)).mul_const (Z-z)).const_add z)
      (((hasDerivAt_id (0 : ℝ)).mul_const (W-w)).const_add w)
      (by simpa using hz) (by simpa using hw) using 1; simp
  have h := hc.le_slope_of_hasDerivAt (y := 1) (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, f, zero_mul, add_zero, one_mul, sub_zero, div_one] at h
  rw [show z+(Z-z)=Z by ring, show w+(W-w)=W by ring] at h
  linarith

lemma normalizedEntropyDz_order {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    normalizedEntropyDz z w ≤ normalizedEntropyDz w z := by
  rcases hzw.eq_or_lt with rfl | hzw
  · rfl
  · have ht := normalizedEntropy_tangent hz hw hw hz
    rw [normalizedEntropy_symm w z] at ht
    nlinarith

lemma hasDerivAt_bose_deriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t => -(bose t * (bose t + 1)))
      (bose z * (bose z + 1) * (2 * bose z + 1)) z := by
  convert! ((hasDerivAt_bose hz).mul ((hasDerivAt_bose hz).add_const 1)).neg using 1; ring

lemma convexOn_bose : ConvexOn ℝ (Ioi 0) bose := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun z hz => (hasDerivAt_bose hz).continuousAt.continuousWithinAt)
    (f' := fun z => -(bose z * (bose z + 1)))
    (f'' := fun z => bose z * (bose z + 1) * (2 * bose z + 1))
  · intro z hz
    exact (hasDerivAt_bose (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    exact (hasDerivAt_bose_deriv (by simpa using hz)).hasDerivWithinAt
  · intro z hz
    have hb := bose_pos (show 0 < z by simpa using hz)
    positivity

lemma bose_tangent {z Z : ℝ} (hz : 0 < z) (hZ : 0 < Z) :
    bose z - bose z * (bose z + 1) * (Z-z) ≤ bose Z := by
  rcases lt_trichotomy z Z with hlt | rfl | hgt
  · have h := convexOn_bose.le_slope_of_hasDerivAt hz hZ hlt (hasDerivAt_bose hz)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith
  · simp
  · have h := convexOn_bose.slope_le_of_hasDerivAt hZ hz hgt (hasDerivAt_bose hz)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith

def canonicalPrice (z w : ℝ) : ℝ := -(8 * normalizedEntropyDz z w)⁻¹

def canonicalGamma (z w : ℝ) : ℝ :=
  (1/8 + canonicalPrice z w * normalizedEntropyDz w z) / (2 * bose w * (bose w + 1))

lemma canonicalPrice_pos {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    0 < canonicalPrice z w := by
  unfold canonicalPrice
  exact neg_pos.mpr (inv_neg''.mpr (mul_neg_of_pos_of_neg (by norm_num) (normalizedEntropyDz_neg hz hw)))

lemma canonicalPrice_gradient {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    1/8 + canonicalPrice z w * normalizedEntropyDz z w = 0 := by
  unfold canonicalPrice
  have h := (normalizedEntropyDz_neg hz hw).ne
  field_simp
  ring

lemma canonicalGamma_nonneg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    0 ≤ canonicalGamma z w := by
  have horder := mul_le_mul_of_nonneg_left (normalizedEntropyDz_order hz hw hzw)
    (canonicalPrice_pos hz hw).le
  have hzero := canonicalPrice_gradient hz hw
  unfold canonicalGamma
  apply div_nonneg (by linarith)
  have h := bose_pos hw
  positivity

lemma canonicalGamma_gradient {z w : ℝ} (_hz : 0 < z) (hw : 0 < w) :
    1/8 + canonicalPrice z w * normalizedEntropyDz w z =
      2 * canonicalGamma z w * bose w * (bose w + 1) := by
  unfold canonicalGamma
  have h := (bose_pos hw).ne'
  have h₁ : bose w + 1 ≠ 0 := by linarith [bose_pos hw]
  field_simp

lemma canonicalGamma_self {z : ℝ} (hz : 0 < z) : canonicalGamma z z = 0 := by
  unfold canonicalGamma
  rw [canonicalPrice_gradient hz hz, zero_div]

lemma canonical_support_normalized {z w Z W : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) (hZ : 0 < Z) (hW : 0 < W) :
    (z+w)/8 + canonicalPrice z w * normalizedEntropy z w +
      canonicalGamma z w * (1 + 2*bose w) ≤
    (Z+W)/8 + canonicalPrice z w * normalizedEntropy Z W +
      canonicalGamma z w * (1 + 2*bose W) := by
  have h₁ := mul_le_mul_of_nonneg_left (normalizedEntropy_tangent hz hw hZ hW)
    (canonicalPrice_pos hz hw).le
  have h₂ := mul_le_mul_of_nonneg_left (bose_tangent hw hW)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (canonicalGamma_nonneg hz hw hzw))
  have hzG := canonicalPrice_gradient hz hw
  have hwG := canonicalGamma_gradient hz hw
  nlinarith [congrArg (fun q : ℝ => q * (Z-z)) hzG,
    congrArg (fun q : ℝ => q * (W-w)) hwG]

lemma entropy_degree {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (s+t) * entropy ((s-t)/(s+t)) =
      (s+t)*Real.log (s+t) - s*Real.log s - t*Real.log t := by
  have hst : s+t ≠ 0 := ne_of_gt (add_pos hs ht)
  rw [entropy_eq_binEntropy]
  rw [show (1+(s-t)/(s+t))/2 = s/(s+t) by field_simp; ring]
  unfold Real.binEntropy
  rw [show 1-s/(s+t)=t/(s+t) by field_simp; ring]
  rw [Real.log_inv, Real.log_inv, Real.log_div hs.ne' hst, Real.log_div ht.ne' hst]
  field_simp
  ring

def joiningZ (x y : ℝ) : ℝ := Real.log ((1+x)/(1+y))
def joiningW (x y : ℝ) : ℝ := Real.log ((1-y)/(1-x))
def joiningCost (x y : ℝ) : ℝ := (x-y)/4 * (Real.artanh x - Real.artanh y)

lemma joiningZ_pos {x y : ℝ} (hy : -1 < y) (hxy : y < x) : 0 < joiningZ x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1+y)).mpr
  linarith

lemma joiningW_pos {x y : ℝ} (hx : x < 1) (hxy : y < x) : 0 < joiningW x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1-x)).mpr
  linarith

lemma bose_joiningZ {x y : ℝ} (hy : -1 < y) (hxy : y < x) :
    bose (joiningZ x y) = (1+y)/(x-y) := by
  have hp : 0 < (1+x)/(1+y) := div_pos (by linarith) (by linarith)
  unfold bose joiningZ
  rw [Real.exp_log hp]
  have hd : 1+y ≠ 0 := by linarith
  rw [show (1+x)/(1+y)-1=(x-y)/(1+y) by field_simp; ring, inv_div]

lemma bose_joiningW {x y : ℝ} (hx : x < 1) (hxy : y < x) :
    bose (joiningW x y) = (1-x)/(x-y) := by
  have hp : 0 < (1-y)/(1-x) := div_pos (by linarith) (by linarith)
  unfold bose joiningW
  rw [Real.exp_log hp]
  have hd : 1-x ≠ 0 := by linarith
  rw [show (1-y)/(1-x)-1=(x-y)/(1-x) by field_simp; ring, inv_div]

lemma joining_order {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) (hm : 0 ≤ x+y) : joiningZ x y ≤ joiningW x y := by
  apply Real.log_le_log (div_pos (by linarith [hx.1]) (by linarith [hy.1]))
  apply (div_le_div_iff₀ (by linarith [hy.1] : 0 < 1+y) (by linarith [hx.2] : 0 < 1-x)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy.le) hm]

lemma normalizedEntropy_actual {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) :
    normalizedEntropy (joiningZ x y) (joiningW x y) = (entropy x + entropy y)/(x-y) := by
  let u := bose (joiningZ x y)
  let v := bose (joiningW x y)
  have hu : 0 < u := bose_pos (joiningZ_pos hy.1 hxy)
  have hv : 0 < v := bose_pos (joiningW_pos hx.2 hxy)
  have hU : u = (1+y)/(x-y) := bose_joiningZ hy.1 hxy
  have hV : v = (1-x)/(x-y) := bose_joiningW hx.2 hxy
  have hd : x-y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hn : 1+u+v = 2/(x-y) := by rw [hU, hV]; field_simp; ring
  have hn' : 1+u+v ≠ 0 := by linarith
  have hX : (u+1-v)/(u+1+v) = x := by
    rw [hU, hV]
    field_simp
    ring
  have hY : (u-(v+1))/(u+(v+1)) = y := by
    rw [hU, hV]
    field_simp
    ring
  have h₁ := entropy_degree (s := u+1) (t := v) (by linarith) hv
  have h₂ := entropy_degree (s := u) (t := v+1) hu (by linarith)
  rw [hX, show u+1+v=1+u+v by ring] at h₁
  rw [hY, show u+(v+1)=1+u+v by ring] at h₂
  change (1+u+v)*Real.log (1+u+v) -
    ((u+1)*Real.log (u+1)+u*Real.log u+(v+1)*Real.log (v+1)+v*Real.log v)/2 = _
  calc
    _ = (1+u+v)*(entropy x+entropy y)/2 := by nlinarith [h₁,h₂]
    _ = _ := by rw [hn]; field_simp

lemma joiningCost_coordinates {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    joiningCost x y = (x-y)*(joiningZ x y + joiningW x y)/8 := by
  unfold joiningCost joiningZ joiningW
  rw [artanh_eq_log_sub hx, artanh_eq_log_sub hy,
    Real.log_div (by linarith [hx.1]) (by linarith [hy.1]),
    Real.log_div (by linarith [hy.2]) (by linarith [hx.2])]
  ring

lemma joiningCost_nonneg {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    0 ≤ joiningCost x y := by
  unfold joiningCost
  rcases le_total y x with h | h
  · apply mul_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))
    exact sub_nonneg.mpr (Real.strictMonoOn_artanh.monotoneOn hy hx h)
  · apply mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by norm_num))
    exact sub_nonpos.mpr (Real.strictMonoOn_artanh.monotoneOn hx hy h)

def coreKappa (z w : ℝ) : ℝ :=
  (z+w)/8 + canonicalPrice z w * normalizedEntropy z w + canonicalGamma z w * (1+2*bose w)

lemma normalizedEntropy_nonneg {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    0 ≤ normalizedEntropy z w := by
  have hgroups : 0 ≤ normalizedEntropy z w - (canonicalQ z + canonicalQ w)/2 := by
    apply hasSum_le (g := canonicalGroup z w) _ hasSum_zero (hasSum_normalizedEntropy hz hw)
    intro n
    unfold canonicalGroup
    positivity
  have hq (t : ℝ) (ht : 0 < t) : 0 ≤ canonicalQ t := by
    unfold canonicalQ
    have hlog : Real.log (1-Real.exp (-t)) ≤ 0 :=
      Real.log_nonpos (by linarith [exp_neg_lt_one ht]) (by linarith [Real.exp_pos (-t)])
    nlinarith [bose_pos ht]
  linarith [hq z hz, hq w hw]

lemma coreKappa_pos {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    0 < coreKappa z w := by
  have h₁ := mul_nonneg (canonicalPrice_pos hz hw).le (normalizedEntropy_nonneg hz hw)
  have h₂ := mul_nonneg (canonicalGamma_nonneg hz hw hzw) (by linarith [bose_pos hw] : 0 ≤ 1+2*bose w)
  unfold coreKappa
  linarith

lemma canonical_support {z w A B : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w)
    (hA : A ∈ Ioo (-1) 1) (hB : B ∈ Ioo (-1) 1) :
    coreKappa z w * (A-B) ≤ joiningCost A B +
      canonicalPrice z w * (entropy A + entropy B) + canonicalGamma z w * (2-A-B) := by
  by_cases hAB : B < A
  · have h := canonical_support_normalized hz hw hzw (joiningZ_pos hB.1 hAB) (joiningW_pos hA.2 hAB)
    have hh := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hAB.le)
    rw [normalizedEntropy_actual hA hB hAB, bose_joiningW hA.2 hAB] at hh
    change coreKappa z w * (A-B) ≤ _ at hh
    rw [joiningCost_coordinates hA hB]
    convert! hh using 1
    have hd : A-B ≠ 0 := ne_of_gt (sub_pos.mpr hAB)
    field_simp
    ring
  · have hleft := mul_nonpos_of_nonneg_of_nonpos (coreKappa_pos hz hw hzw).le
      (sub_nonpos.mpr (le_of_not_gt hAB))
    have hcost := joiningCost_nonneg hA hB
    have hent := mul_nonneg (canonicalPrice_pos hz hw).le
      (add_nonneg (entropy_nonneg ⟨hA.1.le,hA.2.le⟩) (entropy_nonneg ⟨hB.1.le,hB.2.le⟩))
    have hcorner := mul_nonneg (canonicalGamma_nonneg hz hw hzw)
      (show 0 ≤ 2-A-B by linarith [hA.2,hB.2])
    linarith

lemma canonical_core_contact {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) :
    coreKappa (joiningZ x y) (joiningW x y) * (x-y) = joiningCost x y +
      canonicalPrice (joiningZ x y) (joiningW x y) * (entropy x+entropy y) +
      canonicalGamma (joiningZ x y) (joiningW x y) * (2-x-y) := by
  unfold coreKappa
  rw [normalizedEntropy_actual hx hy hxy, bose_joiningW hx.2 hxy, joiningCost_coordinates hx hy]
  have hd : x-y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  field_simp
  ring

lemma averaged_canonical_support {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) {z w : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hzw : z ≤ w) :
    coreKappa z w * (cubeAverage A-cubeAverage B) ≤
      cubeAverage (fun t => joiningCost (A t) (B t)) +
      canonicalPrice z w * (entropyAverage A+entropyAverage B) +
      canonicalGamma z w * (2-cubeAverage A-cubeAverage B) := by
  have h := cubeAverage_mono (fun t => canonical_support hz hw hzw (hA t) (hB t))
  simpa only [cubeAverage_add, cubeAverage_sub, cubeAverage_smul, cubeAverage_const,
    entropyAverage] using h

lemma canonical_core_lower {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) {x y k : ℝ}
    (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) (hxy : y < x) (hm : 0 ≤ x+y)
    (hd : cubeAverage A-cubeAverage B = k*(x-y))
    (he : entropyAverage A+entropyAverage B = k*(entropy x+entropy y))
    (hc : canonicalGamma (joiningZ x y) (joiningW x y) *
      (2-cubeAverage A-cubeAverage B) =
      k*canonicalGamma (joiningZ x y) (joiningW x y)*(2-x-y)) :
    k * joiningCost x y ≤ cubeAverage (fun t => joiningCost (A t) (B t)) := by
  have h := averaged_canonical_support A B hA hB (joiningZ_pos hy.1 hxy) (joiningW_pos hx.2 hxy)
    (joining_order hx hy hxy hm)
  rw [hd, he, hc] at h
  have heq := congrArg (fun q : ℝ => k*q) (canonical_core_contact hx hy hxy)
  nlinarith

def onecornerX (m d k : ℝ) : ℝ := 1-(1-m-d)/k
def onecornerY (m d k : ℝ) : ℝ := 1-(1-m+d)/k
def onecornerEntropy (m d k : ℝ) : ℝ :=
  k*(entropy (onecornerX m d k)+entropy (onecornerY m d k))/2

def reflectedEntropy (d r : ℝ) : ℝ := (d/r)*entropy r

lemma onecorner_domain {m d k : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (hk : k ∈ Icc (1-m) 1) :
    onecornerX m d k ∈ Ioo (-1) 1 ∧ onecornerY m d k ∈ Ioo (-1) 1 ∧
      onecornerY m d k < onecornerX m d k ∧ 0 ≤ onecornerX m d k+onecornerY m d k := by
  have hk0 : 0 < k := by linarith [hk.1]
  have hL : 0 < (1-m-d)/k := div_pos (by linarith) hk0
  have hU : (1-m+d)/k < 2 := (div_lt_iff₀ hk0).mpr (by linarith [hk.1])
  have hXY : (1-m-d)/k < (1-m+d)/k := (div_lt_div_iff_of_pos_right hk0).mpr (by linarith)
  have hsum : (1-m-d)/k+(1-m+d)/k ≤ 2 := by
    rw [← add_div]
    exact (div_le_iff₀ hk0).mpr (by linarith [hk.1])
  unfold onecornerX onecornerY
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,by linarith,by linarith⟩

lemma onecorner_means {m d k : ℝ} (hk : k ≠ 0) :
    m+d = 1-k+k*onecornerX m d k ∧ m-d = 1-k+k*onecornerY m d k := by
  unfold onecornerX onecornerY
  constructor <;> field_simp <;> ring

lemma onecorner_entropy_left {m d : ℝ} (hm : m < 1) :
    onecornerEntropy m d (1-m) = (1-m)*entropy (d/(1-m)) := by
  have hm0 : 1-m ≠ 0 := by linarith
  unfold onecornerEntropy onecornerX onecornerY
  rw [show 1-(1-m-d)/(1-m)=d/(1-m) by field_simp; ring,
    show 1-(1-m+d)/(1-m)=-(d/(1-m)) by field_simp; ring, entropy_neg]
  ring

lemma onecorner_entropy_right (m d : ℝ) :
    onecornerEntropy m d 1 = (entropy (m+d)+entropy (m-d))/2 := by
  unfold onecornerEntropy onecornerX onecornerY
  ring_nf

lemma continuousOn_onecornerEntropy {m d : ℝ} (hm : m < 1) :
    ContinuousOn (onecornerEntropy m d) (Icc (1-m) 1) := by
  intro k hk
  have hk0 : k ≠ 0 := by linarith [hk.1]
  unfold onecornerEntropy onecornerX onecornerY
  have h₁ : ContinuousAt (fun k : ℝ => 1-(1-m-d)/k) k := by fun_prop
  have h₂ : ContinuousAt (fun k : ℝ => 1-(1-m+d)/k) k := by fun_prop
  exact ((continuousAt_id.mul ((continuous_entropy.continuousAt.comp h₁).add
    (continuous_entropy.continuousAt.comp h₂))).div_const 2).continuousWithinAt

lemma exists_onecorner_entropy {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (he0 : (1-m)*entropy (d/(1-m)) ≤ e)
    (he1 : e ≤ (entropy (m+d)+entropy (m-d))/2) :
    ∃ k ∈ Icc (1-m) 1, onecornerEntropy m d k = e := by
  apply intermediate_value_Icc (by linarith : 1-m ≤ 1) (continuousOn_onecornerEntropy (by linarith))
  simpa only [onecorner_entropy_left (by linarith : m<1), onecorner_entropy_right] using ⟨he0,he1⟩

lemma exists_reflected_entropy {m d e : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (he : 0 < e) (he0 : e ≤ (1-m)*entropy (d/(1-m))) :
    ∃ r ∈ Ico (d/(1-m)) 1, reflectedEntropy d r = e := by
  have hm0 : 0 < 1-m := by linarith
  have hr0 : 0 < d/(1-m) := div_pos hd hm0
  have hr1 : d/(1-m) < 1 := (div_lt_one hm0).mpr (by linarith)
  have hc : ContinuousOn (reflectedEntropy d) (Icc (d/(1-m)) 1) := by
    intro r hr
    have hnr : r ≠ 0 := by linarith [hr.1]
    unfold reflectedEntropy
    exact ((continuousAt_const.div continuousAt_id hnr).mul continuous_entropy.continuousAt).continuousWithinAt
  have hleft : reflectedEntropy d (d/(1-m)) = (1-m)*entropy (d/(1-m)) := by
    unfold reflectedEntropy
    field_simp
  have hright : reflectedEntropy d 1 = 0 := by simp [reflectedEntropy]
  obtain ⟨r,hr,hre⟩ := intermediate_value_Icc' hr1.le hc
    (show e ∈ Icc (reflectedEntropy d 1) (reflectedEntropy d (d/(1-m))) by
      rw [hleft,hright]; exact ⟨he.le,he0⟩)
  refine ⟨r,⟨hr.1,lt_of_le_of_ne hr.2 ?_⟩,hre⟩
  intro hrEq
  subst r
  rw [hright] at hre
  linarith

lemma onecorner_cost_lower {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {m d k : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1) (hk : k ∈ Icc (1-m) 1)
    (ha : cubeAverage A = m+d) (hb : cubeAverage B = m-d)
    (he : (entropyAverage A+entropyAverage B)/2 = onecornerEntropy m d k) :
    k*joiningCost (onecornerX m d k) (onecornerY m d k) ≤
      cubeAverage (fun t => joiningCost (A t) (B t)) := by
  obtain ⟨hx,hy,hxy,hcenter⟩ := onecorner_domain hm hd hmd hk
  have hk0 : k ≠ 0 := by linarith [hk.1]
  obtain ⟨hamean,hbmean⟩ := onecorner_means (m := m) (d := d) hk0
  apply canonical_core_lower A B hA hB hx hy hxy hcenter
  · rw [ha,hb]; nlinarith
  · unfold onecornerEntropy at he; linarith
  · rw [ha,hb]
    rw [hamean,hbmean]
    ring

lemma reflected_cost_lower {n : ℕ} (A B : Cube n → ℝ) (hA : IsInterior A) (hB : IsInterior B)
    {r k : ℝ} (hr : r ∈ Ioo 0 1)
    (hd : cubeAverage A-cubeAverage B = 2*k*r)
    (he : (entropyAverage A+entropyAverage B)/2 = k*entropy r) :
    k*joiningCost r (-r) ≤ cubeAverage (fun t => joiningCost (A t) (B t)) := by
  have hx : r ∈ Ioo (-1) 1 := ⟨by linarith [hr.1],hr.2⟩
  have hy : -r ∈ Ioo (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hzw : joiningZ r (-r) = joiningW r (-r) := by simp [joiningZ,joiningW,sub_eq_add_neg]
  have hc : canonicalGamma (joiningZ r (-r)) (joiningW r (-r)) = 0 := by
    rw [← hzw]
    exact canonicalGamma_self (joiningZ_pos hy.1 (by linarith [hr.1]))
  apply canonical_core_lower A B hA hB hx hy (by linarith [hr.1]) (by linarith)
  · rw [hd]; ring
  · rw [entropy_neg]; linarith
  · rw [hc]; ring

end LeanBlast.CourtadeKumar
end
end

end OAI
