import Mathlib

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
section

lemma tf_power_strongConvex {s : ℝ} (_hs : 0 < s) :
    ConvexOn ℝ (Set.Icc 0 s)
      (fun t : ℝ => t ^ (5 / 3 : ℝ) - (5 / 9 : ℝ) * s ^ (-1 / 3 : ℝ) * t ^ 2) := by
  let c : ℝ := (5 / 9 : ℝ) * s ^ (-1 / 3 : ℝ)
  let f' : ℝ → ℝ := fun t => (5 / 3 : ℝ) * t ^ (2 / 3 : ℝ) - 2 * c * t
  let f'' : ℝ → ℝ := fun t => (10 / 9 : ℝ) * t ^ (-1 / 3 : ℝ) - 2 * c
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc _ _)
  · exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 3)).sub
      (continuous_const.mul (continuous_id.pow 2))).continuousOn
  · intro t ht
    have ht' : 0 < t := (Set.mem_Ioo.mp (by simpa only [interior_Icc] using ht)).1
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := (5 / 3 : ℝ)) (Or.inl ht'.ne')
    have h2 := ((hasDerivAt_pow 2 t).const_mul c)
    have hh := (h1.fun_sub h2).hasDerivWithinAt (s := interior (Set.Icc 0 s))
    norm_num at hh
    simpa [f', c, mul_assoc, mul_left_comm, mul_comm] using hh
  · intro t ht
    have ht' : 0 < t := (Set.mem_Ioo.mp (by simpa only [interior_Icc] using ht)).1
    have h1 := (Real.hasDerivAt_rpow_const (x := t) (p := (2 / 3 : ℝ))
      (Or.inl ht'.ne')).const_mul (5 / 3 : ℝ)
    have h2 := (hasDerivAt_id t).const_mul (2 * c)
    have hh := (h1.fun_sub h2).hasDerivWithinAt (s := interior (Set.Icc 0 s))
    norm_num at hh
    convert! hh using 1 <;> simp only [f'', interior_Icc]
    all_goals (norm_num; ring)
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 s := by simpa only [interior_Icc] using ht
    have hp := Real.rpow_le_rpow_of_nonpos ht'.1 ht'.2.le (by norm_num : (-1 / 3 : ℝ) ≤ 0)
    dsimp [f'', c]
    nlinarith

lemma tf_power_midpoint_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (5 / 36 : ℝ) * (a + b) ^ (-1 / 3 : ℝ) * (a - b) ^ 2 ≤
      (a ^ (5 / 3 : ℝ) + b ^ (5 / 3 : ℝ)) / 2 - ((a + b) / 2) ^ (5 / 3 : ℝ) := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hc := tf_power_strongConvex (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs))
  have h := hc.2 (show a ∈ Set.Icc 0 (a + b) by exact ⟨ha, by linarith⟩)
    (show b ∈ Set.Icc 0 (a + b) by exact ⟨hb, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  rw [he] at h
  nlinarith

def tfWeight (a b : ℝ) : ℝ := (a + b) ^ (-1 / 3 : ℝ) * (a - b) ^ 2

lemma tfWeight_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ tfWeight a b :=
  mul_nonneg (Real.rpow_nonneg (add_nonneg ha hb) _) (sq_nonneg _)

lemma tfWeight_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tfWeight a b ≤ (18 / 5 : ℝ) * (a ^ (5 / 3 : ℝ) + b ^ (5 / 3 : ℝ)) := by
  have h := tf_power_midpoint_gap ha hb
  have hn := Real.rpow_nonneg (div_nonneg (add_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2)) (5 / 3 : ℝ)
  dsimp [tfWeight]
  nlinarith

lemma tfWeight_interpolation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ^ (5 / 3 : ℝ) =
      (tfWeight a b) ^ (5 / 6 : ℝ) * ((a + b) ^ (5 / 3 : ℝ)) ^ (1 / 6 : ℝ) := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, tfWeight]
  have hs' : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  rw [tfWeight, Real.mul_rpow (Real.rpow_nonneg hs'.le _) (sq_nonneg _),
    ← Real.rpow_mul hs'.le, ← Real.rpow_mul hs'.le]
  have he : ((a - b) ^ 2) ^ (5 / 6 : ℝ) = |a - b| ^ (5 / 3 : ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg (a - b)) 2]
    norm_num
  rw [he]
  symm
  calc
    _ = |a - b| ^ (5 / 3 : ℝ) *
      ((a + b) ^ ((-1 / 3 : ℝ) * (5 / 6)) * (a + b) ^ ((5 / 3 : ℝ) * (1 / 6))) := by ring
    _ = _ := by rw [← Real.rpow_add hs']; norm_num

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma tf_integrable {f : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) : Integrable (fun x => f x ^ (5 / 3 : ℝ)) μ := by
  have hi := hf.integrable_norm_rpow (by norm_num : (5 / 3 : ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5 / 3 : ENNReal) ≠ ⊤)
  norm_num at hi
  exact hi.congr (hn.mono fun x hx => by simp [abs_of_nonneg hx])

lemma tfWeight_integrable {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    Integrable (fun x => tfWeight (f x) (g x)) μ := by
  have hi := ((tf_integrable hf hnf).add (tf_integrable hg hng)).const_mul (18 / 5 : ℝ)
  apply hi.mono'
  · unfold tfWeight
    exact ((hf.aestronglyMeasurable.add hg.aestronglyMeasurable).aemeasurable.pow_const _).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
  · filter_upwards [hnf, hng] with x hfx hgx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (tfWeight_nonneg hfx hgx), Pi.add_apply] using tfWeight_le hfx hgx

lemma tfWeight_integral_gap {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (5 / 36 : ℝ) * (∫ x, tfWeight (f x) (g x) ∂μ) ≤
      ((∫ x, f x ^ (5 / 3 : ℝ) ∂μ) + (∫ x, g x ^ (5 / 3 : ℝ) ∂μ)) / 2 -
      ∫ x, ((f x + g x) / 2) ^ (5 / 3 : ℝ) ∂μ := by
  have hm : MemLp (fun x => (f x + g x) / 2) (5 / 3) μ := by
    simpa only [div_eq_mul_inv, Pi.add_apply] using (hf.add hg).mul_const (2 : ℝ)⁻¹
  have hnm : ∀ᵐ x ∂μ, 0 ≤ (f x + g x) / 2 := by
    filter_upwards [hnf, hng] with x hx hy
    positivity
  have hh := integral_mono_ae ((tfWeight_integrable hf hg hnf hng).const_mul (5 / 36 : ℝ))
    ((((tf_integrable hf hnf).add (tf_integrable hg hng)).div_const 2).sub (tf_integrable hm hnm))
    (show ∀ᵐ x ∂μ, (5 / 36 : ℝ) * tfWeight (f x) (g x) ≤
      (f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) / 2 - ((f x + g x) / 2) ^ (5 / 3 : ℝ) from by
      filter_upwards [hnf, hng] with x hx hy
      simpa only [tfWeight, mul_assoc] using tf_power_midpoint_gap hx hy)
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  have hsum : Integrable (fun x => f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) μ := by
    exact (tf_integrable hf hnf).add (tf_integrable hg hng)
  have hdiv : Integrable (fun x => (f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) / 2) μ := hsum.div_const 2
  rw [integral_const_mul, integral_sub hdiv (tf_integrable hm hnm), integral_div,
    integral_add (tf_integrable hf hnf) (tf_integrable hg hng)] at hh
  exact hh

lemma integrable_rpow_inv_memLp {w : α → ℝ} (hw : Integrable w μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) {q : ℝ} (hq : 0 < q) :
    MemLp (fun x => w x ^ (1 / q)) (ENNReal.ofReal q) μ := by
  have hm : AEStronglyMeasurable (fun x => w x ^ (1 / q)) μ :=
    (hw.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by positivity) ENNReal.ofReal_ne_top).mp
  apply hw.congr
  filter_upwards [hwn] with x hx
  rw [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx, one_div_mul_cancel hq.ne', Real.rpow_one]

lemma integral_rpow_inv_rpow {w : α → ℝ} (hwn : ∀ᵐ x ∂μ, 0 ≤ w x)
    {q : ℝ} (hq : q ≠ 0) :
    (∫ x, (w x ^ (1 / q)) ^ q ∂μ) = ∫ x, w x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hwn] with x hx
  rw [← Real.rpow_mul hx, one_div_mul_cancel hq, Real.rpow_one]

lemma tfWeight_integral_interpolation {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, |f x - g x| ^ (5 / 3 : ℝ) ∂μ) ≤
      (∫ x, tfWeight (f x) (g x) ∂μ) ^ (5 / 6 : ℝ) *
      (∫ x, (f x + g x) ^ (5 / 3 : ℝ) ∂μ) ^ (1 / 6 : ℝ) := by
  have hsum : ∀ᵐ x ∂μ, 0 ≤ (f + g) x := by
    filter_upwards [hnf, hng] with x hx hy
    exact add_nonneg hx hy
  have hsn : ∀ᵐ x ∂μ, 0 ≤ (f x + g x) ^ (5 / 3 : ℝ) :=
    hsum.mono fun x hx => Real.rpow_nonneg hx _
  have hwn : ∀ᵐ x ∂μ, 0 ≤ tfWeight (f x) (g x) := by
    filter_upwards [hnf, hng] with x hx hy
    exact tfWeight_nonneg hx hy
  have hw := integrable_rpow_inv_memLp (tfWeight_integrable hf hg hnf hng) hwn
    (by norm_num : (0 : ℝ) < 6 / 5)
  have hs := integrable_rpow_inv_memLp (tf_integrable (hf.add hg) hsum) hsn
    (by norm_num : (0 : ℝ) < 6)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (6 / 5 : ℝ).HolderConjugate 6 from Real.holderConjugate_iff.mpr (by norm_num))
    (hwn.mono fun x hx => Real.rpow_nonneg hx (1 / (6 / 5 : ℝ)))
    (hsn.mono fun x hx => Real.rpow_nonneg hx (1 / (6 : ℝ))) hw hs
  rw [integral_rpow_inv_rpow hwn (by norm_num), integral_rpow_inv_rpow hsn (by norm_num)] at hh
  norm_num only [one_div_div, mul_one] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [hnf, hng] with x hx hy
  exact tfWeight_interpolation hx hy

end

open MeasureTheory Filter
open scoped Topology ENNReal

instance tfLpFact : Fact ((1 : ENNReal) ≤ 5 / 3) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

end CoulombAnalysis

end

end OAI
