import OAI.Analysis.HotSpots.Reciprocal

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section DiskFiniteLayer

open Filter Matrix
open scoped Topology
namespace StrictHotSpots.ScalarKernel

lemma choose_recurrence (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose a (n + 1) = (a - n) * Ring.choose a n := by
  have hh := Ring.descPochhammer_eq_factorial_smul_choose a (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    Ring.descPochhammer_eq_factorial_smul_choose] at hh
  simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at hh
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  nlinarith [hh]

def coeff (a : ℝ) (n : ℕ) : ℝ := -(Ring.choose a (n + 2) * (-1) ^ (n + 2))

lemma coeff_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : 0 ≤ coeff a n := by
  induction n with
  | zero =>
    have hh := choose_recurrence a 1
    simp only [Nat.cast_one, Ring.choose_one_right] at hh
    simp only [coeff, zero_add, even_two, Even.neg_pow, one_pow, mul_one]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  | succ n ih =>
    have hh := choose_recurrence a (n + 2)
    have hrec : ((n : ℝ) + 3) * coeff a (n + 1) = ((n : ℝ) + 2 - a) * coeff a n := by
      simp only [coeff, Nat.cast_add, Nat.cast_ofNat] at *
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      nlinarith [congrArg (fun t : ℝ => t * (-1) ^ (n + 2)) hh]
    have hn : 0 < (n : ℝ) + 3 := by positivity
    have hmul : 0 ≤ ((n : ℝ) + 2 - a) * coeff a n :=
      mul_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ih
    nlinarith

lemma binomial_hasSum {a k : ℝ} (hk : |k| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * (-k) ^ n) ((1 - k) ^ a) := by
  have hh := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := -k) (by simpa [Metric.mem_eball, edist_dist, Real.norm_eq_abs] using hk)
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars,
    sub_eq_add_neg, mul_comm] using hh


lemma defect_hasSum {a k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    HasSum (fun n : ℕ => coeff a n * k ^ (n + 1))
      ((1 - (1 - k) ^ a) / k - a) := by
  have hh := binomial_hasSum (a := a) (abs_lt.mpr ⟨by linarith, hk1⟩)
  have ht := (hasSum_nat_add_iff' 2).mpr hh
  have hs := ht.mul_left (-k⁻¹)
  have he : (fun n : ℕ => -k⁻¹ * (Ring.choose a (n + 2) * (-k) ^ (n + 2))) =
      (fun n : ℕ => coeff a n * k ^ (n + 1)) := by
    funext n
    rw [neg_pow k (n + 2)]
    simp only [coeff, pow_add]
    field_simp
  rw [he] at hs
  have hv : -k⁻¹ * ((1 - k) ^ a - ∑ i ∈ Finset.range 2, Ring.choose a i * (-k) ^ i) =
      (1 - (1 - k) ^ a) / k - a := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Ring.choose_zero_right, Ring.choose_one_right, pow_zero, pow_one]
    field_simp
    ring
  rwa [hv] at hs

section Matrix
variable {ι : Type*} [Fintype ι]


lemma posSemidef_entry_pow {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (n : ℕ) :
    (Matrix.of (fun i j => A i j ^ n)).PosSemidef := by
  induction n with
  | zero =>
    simpa [Matrix.vecMulVec] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)))
  | succ n ih =>
    have he : Matrix.of (fun i j => A i j ^ (n + 1)) =
        Matrix.of (fun i j => A i j ^ n) ⊙ A := by
      ext i j
      simp [pow_succ]
    rw [he]
    exact ih.hadamard hA


lemma posSemidef_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => by simpa using (hA n).isHermitian.apply j i)
  · intro x
    have hlimq : Tendsto (fun n => star x ⬝ᵥ A n *ᵥ x) atTop
        (𝓝 (star x ⬝ᵥ B *ᵥ x)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg x)


lemma defect_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hpos : ∀ i j, 0 < A i j) (hlt : ∀ i j, A i j < 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (Matrix.of (fun i j => (1 - (1 - A i j) ^ a) / A i j - a)).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ m ∈ Finset.range n,
      coeff a m • Matrix.of (fun i j => A i j ^ (m + 1)))
  · intro n
    exact Matrix.posSemidef_sum _ (fun m _ =>
      (posSemidef_entry_pow hA _).smul (coeff_nonneg ha ha1 m))
  · intro i j
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      using (defect_hasSum (a := a) (hpos i j) (hlt i j)).tendsto_sum_nat

lemma integral_posSemidef {F : ℝ → Matrix ι ι ℝ}
    (hF : ∀ a ∈ Set.Icc (0 : ℝ) 1, (F a).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun a => F a i j) MeasureTheory.volume 0 1) :
    (Matrix.of (fun i j => ∫ a in (0 : ℝ)..1, F a i j)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ∈ Set.Icc (0 : ℝ) 1 := by simpa using ha
    simpa using (hF a ha').isHermitian.apply i j
  · intro v
    have he : (star v ⬝ᵥ (Matrix.of (fun i j => ∫ a in (0 : ℝ)..1, F a i j)) *ᵥ v) =
        ∫ a in (0 : ℝ)..1, star v ⬝ᵥ F a *ᵥ v := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        · simp only [intervalIntegral.integral_mul_const]
        · intro j _
          exact (hi i j).mul_const _
      · intro i _
        simpa only [Finset.sum_apply] using
          (IntervalIntegrable.sum Finset.univ fun j _ => (hi i j).mul_const (v j)).const_mul (v i)
    rw [he]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro a ha
    exact (hF a ha).dotProduct_mulVec_nonneg v

end Matrix


lemma integral_rpow_parameter {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (∫ a in (0 : ℝ)..1, x ^ a) = (x - 1) / Real.log x := by
  have hl : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx hx1)
  have hh := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.exp) (a := 0) (b := 1) (Real.log x)
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, Real.exp_log hx] at hh
  rw [eq_div_iff hl]
  convert hh using 1
  · simp only [Real.rpow_def_of_pos hx, mul_comm]

lemma integral_defect {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (∫ a in (0 : ℝ)..1, ((1 - (1 - k) ^ a) / k - a)) =
      k⁻¹ - 1 / 2 + (Real.log (1 - k))⁻¹ := by
  have hb : 0 < 1 - k := sub_pos.mpr hk1
  have hcont : Continuous (fun a : ℝ => (1 - k) ^ a) :=
    Real.continuous_const_rpow hb.ne'
  have hi := hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hi1 : IntervalIntegrable (fun a : ℝ => (1 - (1 - k) ^ a) / k)
      MeasureTheory.volume 0 1 :=
    ((continuous_const.sub hcont).div_const k).intervalIntegrable 0 1
  have hiid : IntervalIntegrable (fun a : ℝ => a) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi1 hiid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 1) hi]
  rw [integral_rpow_parameter hb (by linarith)]
  norm_num [intervalIntegral.integral_const, integral_id]
  field_simp
  ring

section Matrix
variable {ι : Type*} [Fintype ι]

lemma logDefect_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hpos : ∀ i j, 0 < A i j) (hlt : ∀ i j, A i j < 1) :
    (Matrix.of (fun i j => (A i j)⁻¹ - 1 / 2 + (Real.log (1 - A i j))⁻¹)).PosSemidef := by
  have hh := integral_posSemidef
    (F := fun a => Matrix.of (fun i j => (1 - (1 - A i j) ^ a) / A i j - a))
    (fun a ha => defect_posSemidef hA hpos hlt ha.1 ha.2)
    (fun i j => (((continuous_const.sub
      (Real.continuous_const_rpow (sub_pos.mpr (hlt i j)).ne')).div_const
        (A i j)).sub continuous_id).intervalIntegrable 0 1)
  simpa only [Matrix.of_apply, integral_defect (hpos _ _) (hlt _ _)] using hh

end Matrix


def dilation (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

lemma dilation_pos (n : ℕ) : 0 < dilation n := by
  have hn : 1 < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hn)

lemma dilation_lt_one (n : ℕ) : dilation n < 1 := by
  have hn : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
  dsimp [dilation]
  linarith

lemma dilation_tendsto : Tendsto dilation atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  unfold dilation
  simpa only [sub_zero] using (tendsto_const_nhds.sub ht.inv_tendsto_atTop :
    Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 (1 - 0)))

lemma invLog_continuousAt_zero : ContinuousAt (fun x : ℝ => (Real.log x)⁻¹) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa only [one_div, Real.log_zero, _root_.inv_zero] using
    Real.tendsto_log_nhdsNE_zero.const_div_atBot 1

lemma logDefect_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n => (dilation n * a)⁻¹ - 1 / 2 +
        (Real.log (1 - dilation n * a))⁻¹) atTop
      (𝓝 (a⁻¹ - 1 / 2 + (Real.log (1 - a))⁻¹)) := by
  have ht : Tendsto (fun n => dilation n * a) atTop (𝓝 a) :=
    by simpa using dilation_tendsto.mul_const a
  apply (ht.inv₀ ha.ne').sub_const (1 / 2) |>.add
  have ht' : Tendsto (fun n => 1 - dilation n * a) atTop (𝓝 (1 - a)) :=
    tendsto_const_nhds.sub ht
  by_cases he : a = 1
  · subst a
    simpa only [Function.comp_def, mul_one, sub_self, Real.log_zero, _root_.inv_zero] using
      invLog_continuousAt_zero.tendsto.comp (by simpa using ht')
  · have hb : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 he)
    have hl : Real.log (1 - a) ≠ 0 := ne_of_lt (Real.log_neg hb (by linarith))
    exact (Real.continuousAt_log hb.ne').tendsto.comp ht' |>.inv₀ hl

lemma logDefect_posSemidef_le {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hpos : ∀ i j, 0 < A i j) (hle : ∀ i j, A i j ≤ 1) :
    (Matrix.of (fun i j => (A i j)⁻¹ - 1 / 2 + (Real.log (1 - A i j))⁻¹)).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => Matrix.of (fun i j => (dilation n * A i j)⁻¹ - 1 / 2 +
      (Real.log (1 - dilation n * A i j))⁻¹))
  · intro n
    exact logDefect_posSemidef (hA.smul (dilation_pos n).le)
      (fun i j => mul_pos (dilation_pos n) (hpos i j))
      (fun i j => lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hle i j) (dilation_pos n).le)
      (by simpa using dilation_lt_one n))
  · intro i j
    exact logDefect_tendsto (hpos i j) (hle i j)

end StrictHotSpots.ScalarKernel





open Matrix Filter Complex
open scoped Topology ComplexOrder ENNReal
namespace StrictHotSpots.DiskKernel

abbrev Disk := {z : ℂ // ‖z‖ < 1}

def h (x y : Disk) : ℝ :=
  ‖(x : ℂ) - y‖ ^ 2 / ((1 - ‖(x : ℂ)‖ ^ 2) * (1 - ‖(y : ℂ)‖ ^ 2))

def logMean (t : ℝ) : ℝ := (Real.log (1 + 1 / t))⁻¹

def f (t : ℝ) : ℝ := t + 1 / 2 - logMean t


def green (x y : Disk) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (1 + 1 / h x y)


def greenExtended (x y : Disk) : ℝ≥0∞ :=
  if x = y then ∞ else ENNReal.ofReal (green x y)


def regularized (ε : ℝ) (x y : Disk) : ℝ :=
  (4 * Real.pi * (h x y + 1 / 2 - (1 - ε) * f (h x y)))⁻¹

lemma disk_weight_pos (x : Disk) : 0 < 1 - ‖(x : ℂ)‖ ^ 2 := by
  have hn := norm_nonneg (x : ℂ)
  have hx := x.property
  nlinarith

lemma h_nonneg (x y : Disk) : 0 ≤ h x y :=
  div_nonneg (sq_nonneg _) (mul_pos (disk_weight_pos x) (disk_weight_pos y)).le

lemma h_pos {x y : Disk} (hxy : x ≠ y) : 0 < h x y := by
  apply div_pos _ (mul_pos (disk_weight_pos x) (disk_weight_pos y))
  exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr hxy)))

@[simp] lemma h_self (x : Disk) : h x x = 0 := by simp [h]
@[simp] lemma logMean_zero : logMean 0 = 0 := by simp [logMean]
@[simp] lemma f_zero : f 0 = 1 / 2 := by simp [f]

lemma complex_posSemidef_of_entrywise_tendsto {ι : Type*} [Fintype ι]
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have hl := (hlim j i).star
    exact tendsto_nhds_unique (hl.congr fun n => (hA n).isHermitian.apply i j) (hlim i j)
  · intro v
    have hq : Tendsto (fun n => star v ⬝ᵥ A n *ᵥ v) atTop (𝓝 (star v ⬝ᵥ B *ᵥ v)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg v)


lemma szego_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (1 - (x i : ℂ) * star (x j : ℂ))⁻¹)).PosSemidef := by
  let A (n : ℕ) : Matrix ι ι ℂ :=
    Matrix.vecMulVec (fun i => (x i : ℂ) ^ n) (star (fun j => (x j : ℂ) ^ n))
  apply complex_posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ m ∈ Finset.range n, A m)
  · intro n
    exact Matrix.posSemidef_sum _ (fun m _ => Matrix.posSemidef_vecMulVec_self_star _)
  · intro i j
    have hn : ‖(x i : ℂ) * star (x j : ℂ)‖ < 1 := by
      rw [norm_mul, norm_star]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (x j).property.le (norm_nonneg _))
        (by simpa using (x i).property)
    have hs := (hasSum_geometric_of_norm_lt_one hn).tendsto_sum_nat
    simpa [A, Matrix.sum_apply, Matrix.vecMulVec, mul_pow] using hs

lemma realPart_posSemidef {ι : Type*} [Fintype ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) : (Matrix.of (fun i j => (A i j).re)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have hh := congrArg Complex.re (hA.isHermitian.apply i j)
    simpa using hh
  · intro v
    have hh := (Complex.nonneg_iff.mp
      (hA.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, map_sum, Complex.mul_re] using hh

lemma disk_cross_identity (x y : ℂ) :
    ‖1 - x * star y‖ ^ 2 = (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) + ‖x - y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normSzego_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (‖1 - (x i : ℂ) * star (x j : ℂ)‖ ^ 2)⁻¹)).PosSemidef := by
  have hh := realPart_posSemidef ((szego_posSemidef x).hadamard
    (szego_posSemidef x).transpose)
  convert hh using 1
  ext i j
  change _ = (((1 - (x i : ℂ) * star (x j : ℂ))⁻¹) *
    (1 - (x j : ℂ) * star (x i : ℂ))⁻¹).re
  rw [show 1 - (x j : ℂ) * star (x i : ℂ) =
    star (1 - (x i : ℂ) * star (x j : ℂ)) by simp [mul_comm]]
  rw [← star_inv₀, Complex.star_def, Complex.mul_conj]
  simp only [Matrix.of_apply, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]

lemma k_identity (x y : Disk) :
    (1 + h x y)⁻¹ = (1 - ‖(x : ℂ)‖ ^ 2) *
      (‖1 - (x : ℂ) * star (y : ℂ)‖ ^ 2)⁻¹ * (1 - ‖(y : ℂ)‖ ^ 2) := by
  rw [disk_cross_identity]
  unfold h
  have hx := disk_weight_pos x
  have hy := disk_weight_pos y
  have hn := sq_nonneg ‖(x : ℂ) - y‖
  field_simp

lemma k_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (1 + h (x i) (x j))⁻¹)).PosSemidef := by
  classical
  have hh := (normSzego_posSemidef x).mul_mul_conjTranspose_same
    (Matrix.diagonal (fun i => (1 - ‖(x i : ℂ)‖ ^ 2)))
  convert hh using 1
  ext i j
  simp [k_identity]

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma f_eq_logDefect {t : ℝ} (ht : 0 ≤ t) :
    f t = ((1 + t)⁻¹)⁻¹ - 1 / 2 + (Real.log (1 - (1 + t)⁻¹))⁻¹ := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    norm_num [f, logMean]
  · have hh : 1 - (1 + t)⁻¹ = (1 + 1 / t)⁻¹ := by
      have : 1 + t ≠ 0 := by positivity
      field_simp
      ring
    rw [hh, Real.log_inv, inv_neg, inv_inv]
    simp only [f, logMean]
    ring

lemma f_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => f (h (x i) (x j)))).PosSemidef := by
  have hh := ScalarKernel.logDefect_posSemidef_le (k_posSemidef x)
    (fun i j => inv_pos.mpr (by have := h_nonneg (x i) (x j); linarith))
    (fun i j => inv_le_one_of_one_le₀ (by have := h_nonneg (x i) (x j); linarith))
  simpa only [Matrix.of_apply, ← f_eq_logDefect (h_nonneg _ _)] using hh

lemma logMean_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logMean t := by
  apply inv_nonneg.mpr
  exact Real.log_nonneg (by have := one_div_nonneg.mpr ht; linarith)

lemma logMean_pos {t : ℝ} (ht : 0 < t) : 0 < logMean t := by
  apply inv_pos.mpr
  exact Real.log_pos (by have := one_div_pos.mpr ht; linarith)

lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t; rw [f_zero]; norm_num
  · have hlo := Real.le_log_one_add_of_nonneg (one_div_nonneg.mpr ht)
    have hi : 2 * (1 / t) / (1 / t + 2) = (t + 1 / 2)⁻¹ := by
      have : 1 / t + 2 ≠ 0 := by positivity
      have : t + 1 / 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [hi] at hlo
    have hbound := (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0 < (t + 1 / 2)⁻¹) hlo)
      (by positivity : 0 < (t + 1 / 2)⁻¹)).mpr hlo
    simpa only [inv_inv, f, logMean, sub_nonneg] using hbound

lemma f_le_half {t : ℝ} (ht : 0 ≤ t) : f t ≤ 1 / 2 := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t; exact le_of_eq f_zero
  · have hlo := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / t)
    have hlog : 0 < Real.log (1 + 1 / t) := by
      exact Real.log_pos (by have := one_div_pos.mpr hp; linarith)
    have hbound := (inv_le_inv₀ (inv_pos.mpr hp) hlog).mpr
      (show Real.log (1 + 1 / t) ≤ t⁻¹ by
      simpa only [add_sub_cancel_left, one_div] using hlo)
    simp only [inv_inv] at hbound
    dsimp [f, logMean]
    linarith

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma f_alt (t : ℝ) : f t = t + 1 / 2 + (Real.log (t / (1 + t)))⁻¹ := by
  by_cases ht : t = 0
  · subst t
    norm_num [f, logMean]
  · have he : 1 + 1 / t = (t / (1 + t))⁻¹ := by
      rw [inv_div]
      field_simp
      ring
    rw [f, logMean, he, Real.log_inv, inv_neg]
    ring

lemma f_continuousAt {t : ℝ} (ht : 0 ≤ t) : ContinuousAt f t := by
  rw [show f = fun t => t + 1 / 2 + (Real.log (t / (1 + t)))⁻¹ from funext f_alt]
  apply (continuousAt_id.add continuousAt_const).add
  have hden : 1 + t ≠ 0 := by positivity
  have hquot : ContinuousAt (fun t : ℝ => t / (1 + t)) t :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) hden
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    exact ScalarKernel.invLog_continuousAt_zero.comp_of_eq hquot (by simp)
  · have hq : 0 < t / (1 + t) := div_pos hp (by positivity)
    have hql : t / (1 + t) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    exact ((Real.continuousAt_log hq.ne').comp (f := fun t : ℝ => t / (1 + t)) hquot).inv₀
      (ne_of_lt (Real.log_neg hq hql))

lemma h_continuous : Continuous (fun p : Disk × Disk => h p.1 p.2) := by
  apply ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).norm.pow 2 |>.div
  · exact (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).norm.pow 2)).mul
      (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).norm.pow 2))
  · intro p
    exact (mul_pos (disk_weight_pos p.1) (disk_weight_pos p.2)).ne'

lemma regularized_denominator {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Disk) :
    ε / 2 ≤ h x y + 1 / 2 - (1 - ε) * f (h x y) := by
  have ht := h_nonneg x y
  have hl := logMean_nonneg ht
  have he : h x y + 1 / 2 - (1 - ε) * f (h x y) =
      ε * (h x y + 1 / 2) + (1 - ε) * logMean (h x y) := by
    dsimp [f]; ring
  rw [he]
  nlinarith [mul_nonneg hε.le ht, mul_nonneg (sub_nonneg.mpr hε1) hl]

lemma regularized_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Disk) :
    0 < regularized ε x y := by
  apply inv_pos.mpr
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (lt_of_lt_of_le (by positivity : 0 < ε / 2) (regularized_denominator hε hε1 x y))

lemma regularized_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Disk) :
    regularized ε x y ≤ (2 * Real.pi * ε)⁻¹ := by
  apply inv_anti₀ (by positivity)
  have hh := mul_le_mul_of_nonneg_left (regularized_denominator hε hε1 x y)
    (le_of_lt (mul_pos (by norm_num : 0 < (4 : ℝ)) Real.pi_pos))
  nlinarith

lemma regularized_continuous {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Continuous (fun p : Disk × Disk => regularized ε p.1 p.2) := by
  have hf : Continuous (fun p : Disk × Disk => f (h p.1 p.2)) :=
    continuous_iff_continuousAt.mpr fun p =>
      (f_continuousAt (h_nonneg p.1 p.2)).comp
        (f := fun p : Disk × Disk => h p.1 p.2) h_continuous.continuousAt
  apply (continuous_const.mul ((h_continuous.add continuous_const).sub
    (continuous_const.mul hf))).inv₀
  intro p
  exact (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (lt_of_lt_of_le (by positivity : 0 < ε / 2)
      (regularized_denominator hε hε1 p.1 p.2))).ne'

lemma regularized_self (ε : ℝ) (x : Disk) :
    regularized ε x x = (2 * Real.pi * ε)⁻¹ := by
  rw [regularized, h_self, f_zero]
  congr 1
  ring

lemma regularized_antitone {ε δ : ℝ} (hε : 0 < ε) (hδ : ε ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Disk) : regularized δ x y ≤ regularized ε x y := by
  apply inv_anti₀
  · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (lt_of_lt_of_le (by positivity : 0 < ε / 2)
        (regularized_denominator hε (hδ.trans hδ1) x y))
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (f_nonneg (h_nonneg x y))]

lemma regularized_tendsto_offDiagonal {x y : Disk} (hxy : x ≠ y) :
    Tendsto (fun ε : ℝ => regularized ε x y) (𝓝 0) (𝓝 (green x y)) := by
  have hl := logMean_pos (h_pos hxy)
  have hh : ContinuousAt (fun ε : ℝ => regularized ε x y) 0 := by
    apply (continuousAt_const.mul (continuousAt_const.sub
      ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))).inv₀
    have he : h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y) = logMean (h x y) := by
      dsimp [f]; ring
    change 4 * Real.pi * (h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y)) ≠ 0
    rw [he]
    positivity
  convert hh.tendsto using 1
  congr 1
  dsimp [regularized, f, logMean, green]
  rw [show h x y + 1 / 2 - (1 - (0 : ℝ)) *
      (h x y + 1 / 2 - (Real.log (1 + 1 / h x y))⁻¹) =
        (Real.log (1 + 1 / h x y))⁻¹ by ring]
  simp only [_root_.mul_inv_rev, inv_inv]
  ring

end StrictHotSpots.DiskKernel




namespace ReciprocalKernel
open Matrix
variable {ι : Type*} [Fintype ι]

lemma onePositiveSquare_smul {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    {a : ℝ} (ha : 0 < a) : OnePositiveSquare (a • A) := by
  have he (x y : ι → ℝ) : pairing (a • A) x y = a * pairing A x y := by
    simp [pairing, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨?_, ?_⟩
  · ext i j
    simpa only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] using
      congrArg (a * ·) (hA.1.apply i j)
  · intro x y hx hxy
    rw [he] at hx hxy ⊢
    exact mul_nonpos_of_nonneg_of_nonpos ha.le
      (hA.2 x y ((mul_pos_iff_of_pos_left ha).mp hx)
        ((mul_eq_zero.mp hxy).resolve_left ha.ne'))

end ReciprocalKernel

namespace StrictHotSpots.DiskKernel
open ReciprocalKernel

lemma lorentz_identity (x y : Disk) :
    (1 - ‖(x : ℂ)‖ ^ 2) * (h x y + 1 / 2) * (1 - ‖(y : ℂ)‖ ^ 2) =
      (1 / 2) * (1 + ‖(x : ℂ)‖ ^ 2) * (1 + ‖(y : ℂ)‖ ^ 2) -
        2 * ((x : ℂ) * star (y : ℂ)).re := by
  have hx := (disk_weight_pos x).ne'
  have hy := (disk_weight_pos y).ne'
  dsimp [h]
  field_simp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma regularized_reciprocal_onePositiveSquare {ι : Type*} [Fintype ι]
    (x : ι → Disk) {ε : ℝ} (hε1 : ε ≤ 1) :
    OnePositiveSquare (Matrix.of (fun i j => (regularized ε (x i) (x j))⁻¹)) := by
  classical
  let w : ι → ℝ := fun i => 1 - ‖(x i : ℂ)‖ ^ 2
  let v : ι → ℝ := fun i => Real.sqrt (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2)
  let G : Matrix ι ι ℝ := Matrix.of fun i j => ((x i : ℂ) * star (x j : ℂ)).re
  let F : Matrix ι ι ℝ := Matrix.of fun i j => f (h (x i) (x j))
  have hG : G.PosSemidef := realPart_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star (fun i => (x i : ℂ)))
  have hF : (Matrix.diagonal w * F * (Matrix.diagonal w).conjTranspose).PosSemidef :=
    (f_posSemidef x).mul_mul_conjTranspose_same _
  have hU := (hG.smul (by norm_num : 0 ≤ (2 : ℝ))).add (hF.smul (sub_nonneg.mpr hε1))
  have hP := onePositiveSquare_rankOne_sub_psd v hU
  have hsqrt : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (1 / 2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  have hn : Matrix.vecMulVec v v - ((2 : ℝ) • G + (1 - ε) •
      (Matrix.diagonal w * F * (Matrix.diagonal w).conjTranspose)) =
      Matrix.of (fun i j => w i *
        (h (x i) (x j) + 1 / 2 - (1 - ε) * f (h (x i) (x j))) * w j) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_conjTranspose,
      star_trivial, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    dsimp [v, G, F]
    have hv : Real.sqrt (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2) *
        (Real.sqrt (1 / 2) * (1 + ‖(x j : ℂ)‖ ^ 2)) =
        (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2) * (1 + ‖(x j : ℂ)‖ ^ 2) := by
      calc
        _ = (Real.sqrt (1 / 2) * Real.sqrt (1 / 2)) *
            (1 + ‖(x i : ℂ)‖ ^ 2) * (1 + ‖(x j : ℂ)‖ ^ 2) := by ring
        _ = _ := by rw [hsqrt]
    rw [hv]
    have hh := lorentz_identity (x i) (x j)
    dsimp [w]
    simp only [starRingEnd_apply]
    rw [sub_add_eq_sub_sub, ← hh]
    ring
  rw [hn] at hP
  have hres := onePositiveSquare_smul (onePositiveSquare_scale hP (fun i => (w i)⁻¹))
    (mul_pos (by norm_num : 0 < (4 : ℝ)) Real.pi_pos)
  convert hres using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, regularized, inv_inv]
  have hi := (disk_weight_pos (x i)).ne'
  have hj := (disk_weight_pos (x j)).ne'
  dsimp [w]
  field_simp

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma regularized_zero (x y : Disk) : regularized 0 x y = green x y := by
  dsimp [regularized, green, f, logMean]
  rw [show h x y + 1 / 2 - (1 - (0 : ℝ)) *
      (h x y + 1 / 2 - (Real.log (1 + 1 / h x y))⁻¹) =
        (Real.log (1 + 1 / h x y))⁻¹ by ring]
  simp only [_root_.mul_inv_rev, inv_inv]
  ring

lemma regularized_le_green {ε : ℝ} (hε : 0 ≤ ε) {x y : Disk} (hxy : x ≠ y) :
    regularized ε x y ≤ green x y := by
  rw [← regularized_zero]
  apply inv_anti₀
  · have hh := logMean_pos (h_pos hxy)
    have he : h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y) = logMean (h x y) := by
      dsimp [f]; ring
    rw [he]
    positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith [mul_nonneg hε (f_nonneg (h_nonneg x y))]

lemma regularized_tendsto_diagonal (x : Disk) :
    Tendsto (fun ε : ℝ => regularized ε x x) (𝓝[>] 0) atTop := by
  simp only [regularized_self]
  have hh := tendsto_inv_nhdsGT_zero.const_mul_atTop
    (by positivity : 0 < (2 * Real.pi)⁻¹)
  simpa only [_root_.mul_inv_rev, mul_comm] using hh


lemma regularized_tendsto (x y : Disk) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (regularized ε x y))
      (𝓝[>] 0) (𝓝 (greenExtended x y)) := by
  by_cases hxy : x = y
  · subst y
    simpa [greenExtended, Function.comp_def] using
      ENNReal.tendsto_ofReal_atTop.comp (regularized_tendsto_diagonal x)
  · simpa only [greenExtended, ite_eq_right hxy, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (green x y)).comp
        ((regularized_tendsto_offDiagonal hxy).mono_left nhdsWithin_le_nhds)


theorem bounded_green_regularization :
    ∃ C : ℝ → Disk → Disk → ℝ,
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        Continuous (fun p : Disk × Disk => C ε p.1 p.2) ∧
        (∀ x y, 0 < C ε x y ∧ C ε x y ≤ (2 * Real.pi * ε)⁻¹) ∧
        (∀ {ι : Type} [Fintype ι] (x : ι → Disk),
          ReciprocalKernel.OnePositiveSquare (Matrix.of (fun i j => (C ε (x i) (x j))⁻¹)))) ∧
      (∀ ε δ, 0 < ε → ε ≤ δ → δ ≤ 1 → ∀ x y, C δ x y ≤ C ε x y) ∧
      (∀ x y, Tendsto (fun ε => ENNReal.ofReal (C ε x y))
        (𝓝[>] 0) (𝓝 (greenExtended x y))) := by
  refine ⟨regularized, ?_, ?_, regularized_tendsto⟩
  · intro ε hε
    exact ⟨regularized_continuous hε.1 hε.2,
      fun x y => ⟨regularized_pos hε.1 hε.2 x y, regularized_le hε.1 hε.2 x y⟩,
      fun {_} [_] x => regularized_reciprocal_onePositiveSquare x hε.2⟩
  · intro ε δ hε hεδ hδ
    exact regularized_antitone hε hεδ hδ

end StrictHotSpots.DiskKernel
end DiskFiniteLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
