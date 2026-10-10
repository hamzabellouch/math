import OAI.Analysis.RotationWeights.WeakSampling

namespace OAI

noncomputable section

universe uι uκ uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

namespace ContinuousCircleWeight
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
namespace Sampling

def geometricFourierSum (H : ℕ) : C(CircleX, ℂ) := ∑ p ∈ Finset.range H, fourier (p : ℤ)

def fejerKernel (H : ℕ) : C(CircleX, ℝ) :=
  ⟨fun x => ‖geometricFourierSum H x‖ ^ 2 / H, by fun_prop⟩

@[simp] lemma geometricFourierSum_apply (H : ℕ) (x : CircleX) :
    geometricFourierSum H x = ∑ p ∈ Finset.range H, fourier (p : ℤ) x := by
  simp [geometricFourierSum]

@[simp] lemma fejerKernel_apply (H : ℕ) (x : CircleX) :
    fejerKernel H x = ‖geometricFourierSum H x‖ ^ 2 / H := by
  rfl

lemma fejerKernel_nonneg (H : ℕ) (x : CircleX) : 0 ≤ fejerKernel H x := by
  rw [fejerKernel_apply]; positivity

lemma integral_fourier_exact (n : ℤ) :
    (∫ x : CircleX, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

lemma fejerKernel_complex_expansion (H : ℕ) (x : CircleX) :
    (fejerKernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H, fourier ((p : ℤ) - q) x := by
  rw [fejerKernel_apply, Complex.ofReal_div, Complex.ofReal_pow,
    ← Complex.mul_conj', geometricFourierSum_apply]
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  simp_rw [← fourier_neg, ← fourier_add, ← sub_eq_add_neg]
  simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

lemma integral_fejerKernel {H : ℕ} (hH : 0 < H) :
    (∫ x : CircleX, fejerKernel H x ∂AddCircle.haarAddCircle) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [fejerKernel_complex_expansion]
  have hi (n : ℤ) : Integrable (fun x : CircleX => fourier n x) AddCircle.haarAddCircle :=
    Integrable.of_bound (fourier _).continuous.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simp [fourier_apply, Circle.norm_coe]))
  have hs (p : ℕ) : Integrable (fun x : CircleX => ∑ q ∈ Finset.range H,
      fourier ((p : ℤ) - q) x) AddCircle.haarAddCircle :=
    integrable_finsetSum _ (fun _ _ => hi _)
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => hs _)]
  simp_rw [integral_finsetSum _ (fun _ _ => hi _), integral_fourier_exact]
  simp only [sub_eq_zero, Int.natCast_inj]
  simp
  rw [Finset.filter_eq_self.mpr (fun a ha => Finset.mem_range.mp ha)]
  simp [hH.ne']

lemma fourier_nat_eq_pow (p : ℕ) (x : CircleX) :
    fourier (p : ℤ) x = fourier 1 x ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma geometricFourierSum_mul (H : ℕ) (x : CircleX) :
    geometricFourierSum H x * (fourier 1 x - 1) = fourier (H : ℤ) x - 1 := by
  simp_rw [geometricFourierSum_apply, fourier_nat_eq_pow]
  exact geom_sum_mul _ _

lemma fejerKernel_mul_chord_sq_le (H : ℕ) (x : CircleX) :
    fejerKernel H x * ‖fourier 1 x - 1‖ ^ 2 ≤ 4 / H := by
  have h := congrArg norm (geometricFourierSum_mul H x)
  rw [norm_mul] at h
  have hn : ‖fourier (H : ℤ) x - 1‖ ≤ 2 := by
    simpa only [fourier_apply, Circle.norm_coe, norm_one, one_add_one_eq_two] using norm_sub_le (fourier (H : ℤ) x) (1 : ℂ)
  rw [fejerKernel_apply]
  have hs : ‖geometricFourierSum H x‖ ^ 2 * ‖fourier 1 x - 1‖ ^ 2 ≤ 4 := by
    rw [← mul_pow, h]
    nlinarith [norm_nonneg (fourier (H : ℤ) x - 1)]
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hs (Nat.cast_nonneg H : (0 : ℝ) ≤ H)

lemma fourier_one_chord_lower (x : CircleX) :
    4 * ‖x‖ ≤ ‖fourier 1 x - 1‖ := by
  let y : ℝ := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).val
  have hy : |y| ≤ 1 / 2 := by
    have he := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).property
    change -(1 / 2 : ℝ) ≤ y ∧ y < -(1 / 2 : ℝ) + 1 at he
    rw [abs_le]; constructor <;> linarith [he.1, he.2]
  have hc : (y : CircleX) = x := AddCircle.coe_equivIco
  have hn : ‖(y : CircleX)‖ = |y| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hy)
  rw [← hc, hn, fourier_coe_apply]
  have he : (2 * Real.pi * Complex.I * (1 : ℤ) * y / (1 : ℝ) : ℂ) =
      Complex.I * (2 * Real.pi * y : ℝ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hyπ : 0 ≤ Real.pi * |y| := mul_nonneg Real.pi_pos.le (abs_nonneg y)
  have hle : Real.pi * |y| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hyπ hle
  have hs' : 2 * |y| ≤ Real.sin (Real.pi * |y|) := by
    convert hs using 1; field_simp
  have ha : |Real.pi * y| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have he' : 2 * Real.pi * y / 2 = Real.pi * y := by ring
  rw [he', Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi ha, abs_mul, abs_of_pos Real.pi_pos]
  linarith

lemma fejerKernel_le_of_norm_ge {H : ℕ} (hH : 0 < H)
    {δ : ℝ} (hδ : 0 < δ) {x : CircleX} (hx : δ ≤ ‖x‖) :
    fejerKernel H x ≤ 1 / (4 * H * δ ^ 2) := by
  have hc := fourier_one_chord_lower x
  have hk := fejerKernel_mul_chord_sq_le H x
  have hn := fejerKernel_nonneg H x
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hs : 16 * δ ^ 2 ≤ ‖fourier 1 x - 1‖ ^ 2 := by
    nlinarith [norm_nonneg x, norm_nonneg (fourier 1 x - 1)]
  have hprod : fejerKernel H x * (16 * δ ^ 2) ≤ 4 / H :=
    (mul_le_mul_of_nonneg_left hs hn).trans hk
  apply (le_div_iff₀ (by positivity : 0 < 4 * (H : ℝ) * δ ^ 2)).mpr
  have hm := (le_div_iff₀ hH').mp hprod
  nlinarith

lemma fourier_eval_sub (n : ℤ) (x t : CircleX) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul]

lemma fejerKernel_le (H : ℕ) (x : CircleX) : fejerKernel H x ≤ H := by
  have hs : ‖geometricFourierSum H x‖ ≤ H := by
    rw [geometricFourierSum_apply]
    calc
      _ ≤ ∑ p ∈ Finset.range H, ‖fourier (p : ℤ) x‖ := norm_sum_le _ _
      _ = H := by simp [fourier_apply, Circle.norm_coe]
  by_cases hH : H = 0
  · simp [hH]
  · rw [fejerKernel_apply, div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hH))]
    nlinarith [norm_nonneg (geometricFourierSum H x)]

lemma integrable_fejer_mul (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    Integrable (fun t => fejerKernel H (x - t) * f t) AddCircle.haarAddCircle := by
  apply hf.bdd_mul (c := (H : ℝ)) (by fun_prop : Continuous (fun t : CircleX => fejerKernel H (x - t))).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
      fejerKernel_le H (x - t))

def fejerApprox (H : ℕ) (f : CircleX → ℝ) (x : CircleX) : ℝ :=
  ∫ t, fejerKernel H (x - t) * f t ∂AddCircle.haarAddCircle

lemma fejerApprox_complex_expansion (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    (fejerApprox H f x : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ Finset.range H, ∑ q ∈ Finset.range H,
        fourier ((p : ℤ) - q) x * fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q) := by
  have hf' : Integrable (fun t => (f t : ℂ)) AddCircle.haarAddCircle := hf.ofReal
  have hi (n : ℤ) : Integrable (fun t => fourier n (x - t) * (f t : ℂ))
      AddCircle.haarAddCircle := by
    apply hf'.bdd_mul (c := 1) (by fun_prop : Continuous (fun t : CircleX => fourier n (x - t))).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simp [fourier_apply, Circle.norm_coe])
  have he (n : ℤ) : (∫ t, fourier n (x - t) * (f t : ℂ) ∂AddCircle.haarAddCircle) =
      fourier n x * fourierCoeff (fun t => (f t : ℂ)) n := by
    simp_rw [fourier_eval_sub, mul_assoc]
    rw [integral_const_mul]
    rfl
  rw [fejerApprox, ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, fejerKernel_complex_expansion,
    mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum (Finset.range H) (fun p _ =>
    integrable_finsetSum (Finset.range H) (fun q _ => hi ((p : ℤ) - q)))]
  simp_rw [integral_finsetSum (Finset.range H) (fun q _ => hi _), he]

lemma fejerApprox_nonneg (H : ℕ) {f : CircleX → ℝ} (hf : ∀ t, 0 ≤ f t)
    (x : CircleX) : 0 ≤ fejerApprox H f x := by
  exact integral_nonneg (fun t => mul_nonneg (fejerKernel_nonneg H _) (hf t))

lemma fejerApprox_le_one {H : ℕ} (hH : 0 < H) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (hf1 : ∀ t, f t ≤ 1) (x : CircleX) :
    fejerApprox H f x ≤ 1 := by
  have hk : Integrable (fun t : CircleX => fejerKernel H t) AddCircle.haarAddCircle :=
    Integrable.of_bound (fejerKernel H).continuous.aestronglyMeasurable H
      (ae_of_all _ (fun t => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
          fejerKernel_le H t))
  calc
    _ ≤ ∫ t : CircleX, fejerKernel H (x - t) ∂AddCircle.haarAddCircle :=
      integral_mono (integrable_fejer_mul H hf x) (hk.comp_sub_left x)
        (fun t => by simpa using mul_le_mul_of_nonneg_left (hf1 t) (fejerKernel_nonneg H _))
    _ = 1 := by rw [integral_sub_left_eq_self, integral_fejerKernel hH]

lemma fejerApprox_local_error {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    {f : CircleX → ℝ} (hf : Integrable f AddCircle.haarAddCircle)
    (hbound : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (x : CircleX)
    (hloc : ∀ t, ‖x - t‖ < δ → f t = f x) :
    |fejerApprox H f x - f x| ≤ 1 / (4 * H * δ ^ 2) := by
  have hk : Integrable (fun t : CircleX => fejerKernel H t) AddCircle.haarAddCircle :=
    Integrable.of_bound (fejerKernel H).continuous.aestronglyMeasurable H
      (ae_of_all _ (fun t => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _)] using
          fejerKernel_le H t))
  have he : fejerApprox H f x - f x =
      ∫ t, fejerKernel H (x - t) * (f t - f x) ∂AddCircle.haarAddCircle := by
    simp_rw [mul_sub]
    rw [integral_sub (integrable_fejer_mul H hf x) ((hk.comp_sub_left x).mul_const _),
      integral_mul_const, integral_sub_left_eq_self, integral_fejerKernel hH, one_mul]
    rfl
  rw [he, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  have hb (t : CircleX) : ‖fejerKernel H (x - t) * (f t - f x)‖ ≤
      1 / (4 * H * δ ^ 2) := by
    by_cases ht : ‖x - t‖ < δ
    · rw [hloc t ht, sub_self, mul_zero, norm_zero]; positivity
    · have hd : |f t - f x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hbound t).1, (hbound t).2, (hbound x).1, (hbound x).2]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg H _), Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hd (fejerKernel_nonneg H _)).trans
        (by simpa using fejerKernel_le_of_norm_ge hH hδ (le_of_not_gt ht))
  calc
    _ ≤ ∫ _t : CircleX, 1 / (4 * (H : ℝ) * δ ^ 2) ∂AddCircle.haarAddCircle :=
      integral_mono ((integrable_fejer_mul H (hf.sub (integrable_const _)) x).norm)
        (integrable_const _) hb
    _ = _ := by simp

def doubleFourier (v w : ℤ) (z : CircleX × CircleX) : ℂ :=
  fourier v z.1 * fourier w z.2

lemma doubleFourier_norm (v w : ℤ) (z : CircleX × CircleX) :
    ‖doubleFourier v w z‖ = 1 := by
  simp [doubleFourier, fourier_apply, Circle.norm_coe]

lemma integrable_doubleFourier (v w : ℤ) (η : Measure (CircleX × CircleX))
    [IsFiniteMeasure η] : Integrable (doubleFourier v w) η := by
  apply Integrable.of_bound (by unfold doubleFourier; fun_prop : Continuous (doubleFourier v w)).aestronglyMeasurable 1
  exact ae_of_all _ (fun z => (doubleFourier_norm v w z).le)

lemma finite_doubleFourier_error {ι : Type uι} (s : Finset ι) (c : ι → ℂ)
    (v w : ι → ℤ) (η : Measure (CircleX × CircleX)) [IsFiniteMeasure η]
    (ε : ℝ) (hmom : ∀ i ∈ s,
      ‖(∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0)‖ ≤ ε) :
    ‖(∫ z, ∑ i ∈ s, c i * doubleFourier (v i) (w i) z ∂η) -
      ∑ i ∈ s, (if v i = 0 ∧ w i = 0 then c i else 0)‖ ≤
        ε * ∑ i ∈ s, ‖c i‖ := by
  classical
  rw [integral_finsetSum s (fun i _ => (integrable_doubleFourier _ _ η).const_mul _)]
  simp_rw [integral_const_mul]
  have he : (∑ i ∈ s, c i * ∫ z, doubleFourier (v i) (w i) z ∂η) -
      ∑ i ∈ s, (if v i = 0 ∧ w i = 0 then c i else 0) =
      ∑ i ∈ s, c i * ((∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0)) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, ‖c i * ((∫ z, doubleFourier (v i) (w i) z ∂η) -
        (if v i = 0 ∧ w i = 0 then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ * ε := Finset.sum_le_sum (fun i hi => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hmom i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma finite_product_fourier_error {ι : Type uι} {κ : Type uκ} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (v : ι → ℤ) (w : κ → ℤ)
    (η : Measure (CircleX × CircleX)) [IsFiniteMeasure η]
    (ε : ℝ) (hmom : ∀ i ∈ s, ∀ k ∈ t,
      ‖(∫ z, doubleFourier (v i) (w k) z ∂η) -
        (if v i = 0 ∧ w k = 0 then 1 else 0)‖ ≤ ε) :
    ‖(∫ z, (∑ i ∈ s, a i * fourier (v i) z.1) *
        (∑ k ∈ t, b k * fourier (w k) z.2) ∂η) -
      (∑ i ∈ s, if v i = 0 then a i else 0) *
        (∑ k ∈ t, if w k = 0 then b k else 0)‖ ≤
      ε * (∑ i ∈ s, ‖a i‖) * ∑ k ∈ t, ‖b k‖ := by
  classical
  have h := finite_doubleFourier_error (s.product t) (fun ik => a ik.1 * b ik.2)
    (fun ik => v ik.1) (fun ik => w ik.2) η ε
    (fun ik hik => hmom ik.1 (Finset.mem_product.mp hik).1 ik.2 (Finset.mem_product.mp hik).2)
  have hi (i : ι) (k : κ) (z : CircleX × CircleX) :
      (a i * b k) * doubleFourier (v i) (w k) z =
      (a i * fourier (v i) z.1) * (b k * fourier (w k) z.2) := by
    unfold doubleFourier; ring
  have hz (i : ι) (k : κ) :
      (if v i = 0 ∧ w k = 0 then a i * b k else 0) =
      (if v i = 0 then a i else 0) * (if w k = 0 then b k else 0) := by
    split_ifs <;> simp_all
  simp only [hi, hz, norm_mul] at h
  simp only [Finset.product_eq_sprod, Finset.sum_product] at h
  simp_rw [← Finset.sum_mul_sum] at h
  simpa only [mul_assoc] using h

lemma fourierCoeff_norm_le_one {f : CircleX → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (hb : ∀ x, ‖f x‖ ≤ 1) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ 1 := by
  unfold fourierCoeff
  calc
    _ ≤ ∫ x, ‖fourier (-n) x • f x‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : CircleX, (1 : ℝ) ∂AddCircle.haarAddCircle :=
      integral_mono ((hf.fourier_smul _).norm) (integrable_const _) (fun x => by
        simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb x)
    _ = 1 := by simp

def fejerFrequency {H : ℕ} (i : Fin H × Fin H) : ℤ := (i.1 : ℕ) - (i.2 : ℕ)

def fejerCoefficient (H : ℕ) (f : CircleX → ℝ) (i : Fin H × Fin H) : ℂ :=
  (H : ℂ)⁻¹ * fourierCoeff (fun t => (f t : ℂ)) (fejerFrequency i)

lemma fejerApprox_fin_expansion (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (x : CircleX) :
    (fejerApprox H f x : ℂ) = ∑ i : Fin H × Fin H,
      fejerCoefficient H f i * fourier (fejerFrequency i) x := by
  rw [fejerApprox_complex_expansion H hf]
  simp only [Fintype.sum_prod_type, fejerCoefficient, fejerFrequency]
  simp_rw [mul_assoc, mul_comm (fourierCoeff _ _) (fourier _ _), ← Finset.mul_sum]
  congr 1
  have hs (p : ℕ) : (∑ q : Fin H, fourier ((p : ℤ) - (q : ℕ)) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - (q : ℕ))) =
      ∑ q ∈ Finset.range H, fourier ((p : ℤ) - q) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q) :=
    Fin.sum_univ_eq_sum_range (fun q : ℕ => fourier ((p : ℤ) - q) x *
      fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q)) H
  simp_rw [hs]
  exact (Fin.sum_univ_eq_sum_range (fun p : ℕ => ∑ q ∈ Finset.range H,
    fourier ((p : ℤ) - q) x * fourierCoeff (fun t => (f t : ℂ)) ((p : ℤ) - q)) H).symm

lemma fejerCoefficient_zero_sum {H : ℕ} (hH : 0 < H) (f : CircleX → ℝ) :
    (∑ i : Fin H × Fin H, if fejerFrequency i = 0 then fejerCoefficient H f i else 0) =
      ∫ t, (f t : ℂ) ∂AddCircle.haarAddCircle := by
  simp only [Fintype.sum_prod_type, fejerFrequency, fejerCoefficient, sub_eq_zero,
    Int.natCast_inj, Fin.val_inj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hH.ne'), one_mul]
  simp [fourierCoeff]

lemma fejerCoefficient_norm_sum_le {H : ℕ} (hH : 0 < H) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) (hb : ∀ t, |f t| ≤ 1) :
    (∑ i : Fin H × Fin H, ‖fejerCoefficient H f i‖) ≤ H := by
  have hf' : Integrable (fun t => (f t : ℂ)) AddCircle.haarAddCircle := hf.ofReal
  have hcoef (i : Fin H × Fin H) : ‖fejerCoefficient H f i‖ ≤ (H : ℝ)⁻¹ := by
    unfold fejerCoefficient
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    simpa using mul_le_mul_of_nonneg_left (fourierCoeff_norm_le_one hf'
      (fun t => by simpa using hb t) (fejerFrequency i)) (inv_nonneg.mpr (Nat.cast_nonneg H))
  calc
    _ ≤ ∑ _i : Fin H × Fin H, (H : ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hcoef i)
    _ = (H : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      rw [mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hH.ne'), mul_one]

lemma fejerFrequency_abs_lt {H : ℕ} (i : Fin H × Fin H) : |fejerFrequency i| < H := by
  have hp := i.1.isLt
  have hq := i.2.isLt
  rw [fejerFrequency, abs_lt]
  constructor <;> omega

lemma fejer_product_fourier_error {H : ℕ} (hH : 0 < H)
    {f g : CircleX → ℝ} (hf : Integrable f AddCircle.haarAddCircle)
    (hg : Integrable g AddCircle.haarAddCircle)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1)
    (η : Measure (CircleX × CircleX)) [IsProbabilityMeasure η]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmom : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      ‖∫ z, doubleFourier v w z ∂η‖ ≤ ε) :
    ‖(∫ z, (fejerApprox H f z.1 : ℂ) * (fejerApprox H g z.2 : ℂ) ∂η) -
      (∫ t, (f t : ℂ) ∂AddCircle.haarAddCircle) *
      (∫ t, (g t : ℂ) ∂AddCircle.haarAddCircle)‖ ≤ H ^ 2 * ε := by
  classical
  have hm (i k : Fin H × Fin H) :
      ‖(∫ z, doubleFourier (fejerFrequency i) (fejerFrequency k) z ∂η) -
        (if fejerFrequency i = 0 ∧ fejerFrequency k = 0 then 1 else 0)‖ ≤ ε := by
    by_cases hz : fejerFrequency i = 0 ∧ fejerFrequency k = 0
    · simpa [hz.1, hz.2, doubleFourier, fourier_zero, measure_univ] using hε
    · simpa [hz] using hmom _ _ (fejerFrequency_abs_lt i) (fejerFrequency_abs_lt k) hz
  have h := finite_product_fourier_error Finset.univ Finset.univ
    (fejerCoefficient H f) (fejerCoefficient H g) fejerFrequency fejerFrequency η ε
    (fun i _ k _ => hm i k)
  simp_rw [← fejerApprox_fin_expansion H hf, ← fejerApprox_fin_expansion H hg,
    fejerCoefficient_zero_sum hH] at h
  refine h.trans ?_
  calc
    _ ≤ ε * (H : ℝ) * H := mul_le_mul
      (mul_le_mul_of_nonneg_left (fejerCoefficient_norm_sum_le hH hf hfb) hε)
      (fejerCoefficient_norm_sum_le hH hg hgb)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

lemma continuous_fejerApprox (H : ℕ) {f : CircleX → ℝ}
    (hf : Integrable f AddCircle.haarAddCircle) : Continuous (fejerApprox H f) := by
  have he : fejerApprox H f = fun x =>
      (∑ i : Fin H × Fin H, fejerCoefficient H f i * fourier (fejerFrequency i) x).re := by
    funext x
    rw [← fejerApprox_fin_expansion H hf x]
    rfl
  rw [he]
  exact Complex.continuous_re.comp (continuous_finsetSum _
    (fun i _ => continuous_const.mul (fourier (fejerFrequency i)).continuous))

lemma fejer_unsmoothed_error {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    {f g : CircleX → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (Bf Bg : Set CircleX) (hBf : MeasurableSet Bf) (hBg : MeasurableSet Bg)
    (hfloc : ∀ x ∉ Bf, ∀ t, ‖x - t‖ < δ → f t = f x)
    (hgloc : ∀ x ∉ Bg, ∀ t, ‖x - t‖ < δ → g t = g x)
    (η : Measure (CircleX × CircleX)) [IsProbabilityMeasure η] :
    |(∫ z, f z.1 * g z.2 ∂η) -
      (∫ z, fejerApprox H f z.1 * fejerApprox H g z.2 ∂η)| ≤
      η.real (Prod.fst ⁻¹' Bf) + η.real (Prod.snd ⁻¹' Bg) + 2 / (4 * H * δ ^ 2) := by
  have hfi : Integrable f AddCircle.haarAddCircle :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hfb x).1] using (hfb x).2))
  have hgi : Integrable g AddCircle.haarAddCircle :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hgb x).1] using (hgb x).2))
  have hF (x : CircleX) : 0 ≤ fejerApprox H f x ∧ fejerApprox H f x ≤ 1 :=
    ⟨fejerApprox_nonneg H (fun t => (hfb t).1) x,
      fejerApprox_le_one hH hfi (fun t => (hfb t).2) x⟩
  have hG (x : CircleX) : 0 ≤ fejerApprox H g x ∧ fejerApprox H g x ≤ 1 :=
    ⟨fejerApprox_nonneg H (fun t => (hgb t).1) x,
      fejerApprox_le_one hH hgi (fun t => (hgb t).2) x⟩
  have hir : Integrable (fun z : CircleX × CircleX => f z.1 * g z.2) η :=
    Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable 1
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfb z.1).1 (hgb z.2).1)]
        exact (mul_le_of_le_one_left (hgb z.2).1 (hfb z.1).2).trans (hgb z.2).2))
  have his : Integrable (fun z : CircleX × CircleX =>
      fejerApprox H f z.1 * fejerApprox H g z.2) η :=
    Integrable.of_bound (((continuous_fejerApprox H hfi).comp continuous_fst).mul
      ((continuous_fejerApprox H hgi).comp continuous_snd)).aestronglyMeasurable 1
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF z.1).1 (hG z.2).1)]
        exact (mul_le_of_le_one_left (hG z.2).1 (hF z.1).2).trans (hG z.2).2))
  have hdefect (u : CircleX → ℝ) (hu : Integrable u AddCircle.haarAddCircle)
      (hb : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (B : Set CircleX)
      (hloc : ∀ x ∉ B, ∀ t, ‖x-t‖ < δ → u t = u x) (x : CircleX) :
      |u x - fejerApprox H u x| ≤ B.indicator (fun _ => (1 : ℝ)) x +
        1 / (4 * H * δ ^ 2) := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hnonneg := fejerApprox_nonneg H (fun t => (hb t).1) x
      have hone := fejerApprox_le_one hH hu (fun t => (hb t).2) x
      have : |u x - fejerApprox H u x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      exact this.trans (le_add_of_nonneg_right (by positivity))
    · rw [Set.indicator_of_notMem hx, zero_add, abs_sub_comm]
      exact fejerApprox_local_error hH hδ hu hb x (hloc x hx)
  have hpoint (z : CircleX × CircleX) :
      |f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2| ≤
      (Prod.fst ⁻¹' Bf).indicator (fun _ => (1 : ℝ)) z +
      (Prod.snd ⁻¹' Bg).indicator (fun _ => (1 : ℝ)) z + 2 / (4 * H * δ ^ 2) := by
    have he : f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2 =
      (f z.1 - fejerApprox H f z.1) * g z.2 +
      fejerApprox H f z.1 * (g z.2 - fejerApprox H g z.2) := by ring
    have hb := abs_add_le ((f z.1 - fejerApprox H f z.1) * g z.2)
      (fejerApprox H f z.1 * (g z.2 - fejerApprox H g z.2))
    rw [← he, abs_mul, abs_mul, abs_of_nonneg (hgb z.2).1,
      abs_of_nonneg (hF z.1).1] at hb
    have hb1 := mul_le_mul_of_nonneg_left (hgb z.2).2 (abs_nonneg (f z.1 - fejerApprox H f z.1))
    have hb2 := mul_le_mul_of_nonneg_right (hF z.1).2 (abs_nonneg (g z.2 - fejerApprox H g z.2))
    have h1 := hdefect f hfi hfb Bf hfloc z.1
    have h2 := hdefect g hgi hgb Bg hgloc z.2
    change |f z.1 * g z.2 - fejerApprox H f z.1 * fejerApprox H g z.2| ≤
      Bf.indicator (fun _ => (1 : ℝ)) z.1 + Bg.indicator (fun _ => (1 : ℝ)) z.2 +
      2 / (4 * H * δ ^ 2)
    have hsum := hb.trans (add_le_add hb1 hb2)
    simp only [mul_one, one_mul] at hsum
    exact hsum.trans (by convert add_le_add h1 h2 using 1; ring)
  have hi1 : Integrable ((Prod.fst ⁻¹' Bf).indicator (fun _ => (1 : ℝ))) η :=
    (integrable_const _).indicator (hBf.preimage measurable_fst)
  have hi2 : Integrable ((Prod.snd ⁻¹' Bg).indicator (fun _ => (1 : ℝ))) η :=
    (integrable_const _).indicator (hBg.preimage measurable_snd)
  rw [← integral_sub hir his]
  refine (abs_integral_le_integral_abs).trans ((integral_mono
    (hir.sub his).norm ((hi1.add hi2).add (integrable_const _)) hpoint).trans ?_)
  rw [integral_add' (hi1.add hi2) (integrable_const _), integral_add' hi1 hi2]
  rw [integral_indicator_const 1 (hBf.preimage measurable_fst),
    integral_indicator_const 1 (hBg.preimage measurable_snd)]
  simp only [Measure.real, integral_const, measure_univ,
    ENNReal.toReal_one, smul_eq_mul, mul_one, one_mul, le_refl]

def arcBoundary (c : CircleX) (r δ : ℝ) : Set CircleX :=
  Metric.closedBall c (r + δ) \ Metric.ball c (r - δ)

lemma measurableSet_arcBoundary (c : CircleX) (r δ : ℝ) :
    MeasurableSet (arcBoundary c r δ) :=
  Metric.isClosed_closedBall.measurableSet.diff Metric.isOpen_ball.measurableSet

lemma haarAddCircle_one_eq_volume :
    (AddCircle.haarAddCircle : Measure CircleX) = volume := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm

lemma arcBoundary_measure_le (c : CircleX) (r : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (AddCircle.haarAddCircle : Measure CircleX).real (arcBoundary c r δ) ≤ 4 * δ := by
  rw [haarAddCircle_one_eq_volume, arcBoundary, measureReal_sdiff
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)))
    Metric.isOpen_ball.measurableSet]
  rw [← measureReal_congr (AddCircle.closedBall_ae_eq_ball (x := c) (ε := r - δ))]
  simp only [Measure.real, AddCircle.volume_closedBall, ENNReal.toReal_ofReal']
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma arc_indicator_locally_constant (c : CircleX) (r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x : CircleX) (hx : x ∉ arcBoundary c r δ) (t : CircleX) (ht : ‖x - t‖ < δ) :
    (Metric.ball c r).indicator (fun _ => (1 : ℝ)) t =
      (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := by
  classical
  rw [← dist_eq_norm] at ht
  have hd := abs_dist_sub_le x t c
  rw [abs_le] at hd
  by_cases hi : dist x c < r - δ
  · have hix : x ∈ Metric.ball c r := by rw [Metric.mem_ball]; linarith
    have hit : t ∈ Metric.ball c r := by rw [Metric.mem_ball]; linarith [hd.2]
    rw [Set.indicator_of_mem hix, Set.indicator_of_mem hit]
  · have ho : r + δ < dist x c := by
      simp only [arcBoundary, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        not_and, not_lt] at hx
      exact lt_of_not_ge (fun h => hi (lt_of_not_ge (hx h)))
    have hox : x ∉ Metric.ball c r := by rw [Metric.mem_ball, not_lt]; linarith
    have hot : t ∉ Metric.ball c r := by rw [Metric.mem_ball, not_lt]; linarith [hd.2]
    rw [Set.indicator_of_notMem hox, Set.indicator_of_notMem hot]

lemma arc_rectangle_discrepancy {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ)
    (c d : CircleX) (r s : ℝ) (η : Measure (CircleX × CircleX))
    [IsProbabilityMeasure η] {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hfst : ∀ B : Set CircleX, MeasurableSet B →
      η.real (Prod.fst ⁻¹' B) ≤ C * AddCircle.haarAddCircle.real B)
    (hsnd : ∀ B : Set CircleX, MeasurableSet B →
      η.real (Prod.snd ⁻¹' B) ≤ C * AddCircle.haarAddCircle.real B)
    (hmom : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      ‖∫ z, doubleFourier v w z ∂η‖ ≤ ε) :
    |η.real (Metric.ball c r ×ˢ Metric.ball d s) -
      AddCircle.haarAddCircle.real (Metric.ball c r) *
      AddCircle.haarAddCircle.real (Metric.ball d s)| ≤
      8 * C * δ + 2 / (4 * H * δ ^ 2) + H ^ 2 * ε := by
  classical
  let f := (Metric.ball c r).indicator (fun _ => (1 : ℝ))
  let g := (Metric.ball d s).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hg : Measurable g := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hfb (x) : 0 ≤ f x ∧ f x ≤ 1 := by
    dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have hgb (x) : 0 ≤ g x ∧ g x ≤ 1 := by
    dsimp [g, Set.indicator]; split_ifs <;> norm_num
  have hfi : Integrable f AddCircle.haarAddCircle :=
    (integrable_const _).indicator Metric.isOpen_ball.measurableSet
  have hgi : Integrable g AddCircle.haarAddCircle :=
    (integrable_const _).indicator Metric.isOpen_ball.measurableSet
  have h1 := fejer_unsmoothed_error hH hδ hf hg hfb hgb
    (arcBoundary c r δ) (arcBoundary d s δ) (measurableSet_arcBoundary ..)
    (measurableSet_arcBoundary ..) (arc_indicator_locally_constant c r hδ)
    (arc_indicator_locally_constant d s hδ) η
  have h2 := fejer_product_fourier_error hH hfi hgi
    (fun x => by rw [abs_of_nonneg (hfb x).1]; exact (hfb x).2)
    (fun x => by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2) η hε hmom
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h2
  have hm1 := (hfst _ (measurableSet_arcBoundary c r δ)).trans
    (mul_le_mul_of_nonneg_left (arcBoundary_measure_le c r hδ.le) hC)
  have hm2 := (hsnd _ (measurableSet_arcBoundary d s δ)).trans
    (mul_le_mul_of_nonneg_left (arcBoundary_measure_le d s hδ.le) hC)
  have hsum := (abs_sub_le (∫ z, f z.1 * g z.2 ∂η)
    (∫ z, fejerApprox H f z.1 * fejerApprox H g z.2 ∂η)
    ((∫ t, f t ∂AddCircle.haarAddCircle) * ∫ t, g t ∂AddCircle.haarAddCircle)).trans
      (add_le_add h1 h2)
  have hprod : (fun z : CircleX × CircleX => f z.1 * g z.2) =
      (Metric.ball c r ×ˢ Metric.ball d s).indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hzc : z.1 ∈ Metric.ball c r <;>
      by_cases hzd : z.2 ∈ Metric.ball d s <;> simp [f, g, hzc, hzd]
  rw [hprod, integral_indicator_const 1 (Metric.isOpen_ball.measurableSet.prod Metric.isOpen_ball.measurableSet)] at hsum
  dsimp [f, g] at hsum
  rw [integral_indicator_const 1 Metric.isOpen_ball.measurableSet,
    integral_indicator_const 1 Metric.isOpen_ball.measurableSet] at hsum
  simp only [smul_eq_mul, mul_one] at hsum
  linarith

lemma periodic_integral_bounds {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hi : ∀ a b, IntervalIntegrable f volume a b) (hn : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) :
    (b - a - 1) * (∫ x in a..a+1, f x) ≤ ∫ x in a..b, f x ∧
    (∫ x in a..b, f x) ≤ (b - a + 1) * (∫ x in a..a+1, f x) := by
  let n : ℕ := ⌊b - a⌋₊
  have hnl : (n : ℝ) ≤ b - a := Nat.floor_le (sub_nonneg.mpr hab)
  have hnu : b - a < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : 0 ≤ ∫ x in a..a+1, f x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hn x)
  have he (k : ℕ) : (∫ x in a..a+k, f x) = k * ∫ x in a..a+1, f x := by
    simpa using hp.intervalIntegral_add_zsmul_eq (k : ℤ) a hi
  have hlo : (∫ x in a..a+n, f x) ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_interval le_rfl (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
      (ae_of_all _ hn) (hi a b)
  have hup : (∫ x in a..b, f x) ≤ ∫ x in a..a+(n+1 : ℕ), f x :=
    intervalIntegral.integral_mono_interval le_rfl hab (by push_cast; linarith)
      (ae_of_all _ hn) (hi a _)
  rw [he n] at hlo
  rw [he (n+1)] at hup
  push_cast at hup
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hm) hlo
  · exact le_trans hup (mul_le_mul_of_nonneg_right (by linarith) hm)

def intervalLaw (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b-a))⁻¹ • volume.restrict (Ioc a b)

lemma intervalLaw_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  constructor
  simp only [intervalLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using sub_pos.mpr hab) ENNReal.ofReal_ne_top

lemma integral_intervalLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ x, f x ∂intervalLaw a b) = (b-a)⁻¹ • ∫ x in a..b, f x := by
  rw [intervalLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), intervalIntegral.integral_of_le hab]

lemma intervalIntegrable_circle_comp {f : CircleX → ℝ}
    (hf : Integrable f (volume : Measure CircleX)) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => f x) volume a b := by
  have hp : Function.Periodic (fun x : ℝ => f x) 1 := by
    intro x
    simp only [AddCircle.coe_add_period]
  apply hp.intervalIntegrable₀ (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  simpa only [zero_add, Function.comp_def, IntegrableOn] using
    (hmp.integrable_comp hf.aestronglyMeasurable).mpr hf

lemma circle_scaled_integral_bounds {f : CircleX → ℝ}
    (hf : Integrable f (volume : Measure CircleX)) (hn : ∀ x, 0 ≤ f x)
    {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    (1 - 1/(c*(b-a))) * (∫ x, f x) ≤
      (∫ x, f ((c*x : ℝ) : CircleX) ∂intervalLaw a b) ∧
    (∫ x, f ((c*x : ℝ) : CircleX) ∂intervalLaw a b) ≤
      (1 + 1/(c*(b-a))) * (∫ x, f x) := by
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hp : Function.Periodic (fun x : ℝ => f x) 1 := by
    intro x
    simp only [AddCircle.coe_add_period]
  have h := periodic_integral_bounds hp (intervalIntegrable_circle_comp hf)
    (fun x => hn x) (mul_le_mul_of_nonneg_left hab.le hc.le)
  rw [AddCircle.intervalIntegral_preimage] at h
  rw [integral_intervalLaw _ hab.le,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ => f (x : CircleX)) hc.ne']
  simp only [smul_eq_mul]
  constructor
  · have ht := mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ (b-a)⁻¹*c⁻¹)
    convert! ht using 1 <;> field_simp
  · have ht := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ (b-a)⁻¹*c⁻¹)
    convert! ht using 1 <;> field_simp

def phasePair (c d : ℝ) (t : ℝ) : CircleX × CircleX :=
  (((c*t : ℝ) : CircleX), ((d*t : ℝ) : CircleX))

def phasePairLaw (a b c d : ℝ) : Measure (CircleX × CircleX) :=
  (intervalLaw a b).map (phasePair c d)

lemma continuous_phasePair (c d : ℝ) : Continuous (phasePair c d) := by
  unfold phasePair
  fun_prop

lemma phasePairLaw_probability {a b : ℝ} (hab : a < b) (c d : ℝ) :
    IsProbabilityMeasure (phasePairLaw a b c d) := by
  let := intervalLaw_probability hab
  unfold phasePairLaw
  infer_instance

lemma integral_phasePairLaw {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : CircleX × CircleX → E) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (phasePairLaw a b c d)) :
    (∫ z, f z ∂phasePairLaw a b c d) = ∫ t, f (phasePair c d t) ∂intervalLaw a b := by
  exact integral_map (continuous_phasePair c d).aemeasurable hf

lemma phasePairLaw_marginal_fst {a b c d : ℝ} (hab : a < b) (hc : 0 < c)
    (B : Set CircleX) (hB : MeasurableSet B) :
    (phasePairLaw a b c d).real (Prod.fst ⁻¹' B) ≤
      (1 + 1/(c*(b-a))) * (volume : Measure CircleX).real B := by
  classical
  let f := B.indicator (fun _ => (1 : ℝ))
  have hfi : Integrable f (volume : Measure CircleX) := (integrable_const _).indicator hB
  have hfn : ∀ x, 0 ≤ f x := by intro x; dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have h := (circle_scaled_integral_bounds hfi hfn hab hc).2
  have he : (∫ z, (Prod.fst ⁻¹' B).indicator (fun _ => (1 : ℝ)) z
      ∂phasePairLaw a b c d) = ∫ t, f ((c*t : ℝ) : CircleX) ∂intervalLaw a b := by
    rw [integral_phasePairLaw _ ((measurable_const.indicator (hB.preimage measurable_fst)).aestronglyMeasurable)]
    rfl
  rw [integral_indicator_const 1 (hB.preimage measurable_fst)] at he
  dsimp [f] at h
  rw [integral_indicator_const 1 hB] at h
  simp only [smul_eq_mul, mul_one] at he h
  rw [he]
  exact h

lemma phasePairLaw_marginal_snd {a b c d : ℝ} (hab : a < b) (hd : 0 < d)
    (B : Set CircleX) (hB : MeasurableSet B) :
    (phasePairLaw a b c d).real (Prod.snd ⁻¹' B) ≤
      (1 + 1/(d*(b-a))) * (volume : Measure CircleX).real B := by
  classical
  let f := B.indicator (fun _ => (1 : ℝ))
  have hfi : Integrable f (volume : Measure CircleX) := (integrable_const _).indicator hB
  have hfn : ∀ x, 0 ≤ f x := by intro x; dsimp [f, Set.indicator]; split_ifs <;> norm_num
  have h := (circle_scaled_integral_bounds hfi hfn hab hd).2
  have he : (∫ z, (Prod.snd ⁻¹' B).indicator (fun _ => (1 : ℝ)) z
      ∂phasePairLaw a b c d) = ∫ t, f ((d*t : ℝ) : CircleX) ∂intervalLaw a b := by
    rw [integral_phasePairLaw _ ((measurable_const.indicator (hB.preimage measurable_snd)).aestronglyMeasurable)]
    rfl
  rw [integral_indicator_const 1 (hB.preimage measurable_snd)] at he
  dsimp [f] at h
  rw [integral_indicator_const 1 hB] at h
  simp only [smul_eq_mul, mul_one] at he h
  rw [he]
  exact h

lemma phasePair_fourier (c d t : ℝ) (v w : ℤ) :
    fourier v (phasePair c d t).1 * fourier w (phasePair c d t).2 =
      Complex.exp ((2 * Real.pi * ((v : ℝ)*c+(w : ℝ)*d) : ℝ) * Complex.I * t) := by
  simp only [phasePair, fourier_coe_apply, Complex.ofReal_one, div_one, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma intervalLaw_exponential_bound {a b ω : ℝ} (hab : a < b) (hω : ω ≠ 0) :
    ‖∫ t : ℝ, Complex.exp ((2 * Real.pi * ω : ℝ) * Complex.I * t)
      ∂intervalLaw a b‖ ≤ 1/(Real.pi*|ω| *(b-a)) := by
  have hc : (2 * Real.pi * ω : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hω) Complex.I_ne_zero
  rw [integral_intervalLaw _ hab.le]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [integral_exp_mul_complex hc, norm_smul, norm_div]
  have hn (x : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * x)‖ = 1 := by
    have he : 2 * (Real.pi : ℂ) * ω * Complex.I * x =
        ((2 * Real.pi * ω * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hnum := (norm_sub_le (Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * b))
    (Complex.exp (2 * (Real.pi : ℂ) * ω * Complex.I * a)))
  rw [hn b, hn a] at hnum
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_inv, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ (b-a)⁻¹ * ((1+1)/(2*Real.pi*|ω|)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

lemma phasePairLaw_fourier_bound {a b c d : ℝ} (hab : a < b) (v w : ℤ)
    (hfreq : (v : ℝ)*c+(w : ℝ)*d ≠ 0) :
    ‖∫ z, fourier v z.1 * fourier w z.2 ∂phasePairLaw a b c d‖ ≤
      1/(Real.pi*|(v : ℝ)*c+(w : ℝ)*d| *(b-a)) := by
  rw [integral_phasePairLaw _ (by fun_prop)]
  simp_rw [phasePair_fourier]
  exact intervalLaw_exponential_bound hab hfreq

lemma separated_phase_rectangle_bound {a b c d C R : ℝ}
    (hab : a < b) (hc : 0 < c) (hd : 0 < d) (hR : 0 < R)
    (hC0 : 0 ≤ C) (hCc : 1 + 1/(c*(b-a)) ≤ C)
    (hCd : 1 + 1/(d*(b-a)) ≤ C) {H : ℕ} (hH : 0 < H)
    (hsep : ∀ v w : ℤ, |v| < H → |w| < H → ¬(v = 0 ∧ w = 0) →
      R ≤ |(v : ℝ)*c + (w : ℝ)*d|)
    {δ : ℝ} (hδ : 0 < δ) (x y : CircleX) (r s : ℝ) :
    |(phasePairLaw a b c d).real (Metric.ball x r ×ˢ Metric.ball y s) -
      volume.real (Metric.ball x r) * volume.real (Metric.ball y s)| ≤
      8*C*δ + 2/(4*H*δ^2) + H^2/(Real.pi*R*(b-a)) := by
  let := phasePairLaw_probability hab c d
  have hε : 0 ≤ 1/(Real.pi*R*(b-a)) := by positivity
  have hfst (B : Set CircleX) (hB : MeasurableSet B) :
      (phasePairLaw a b c d).real (Prod.fst ⁻¹' B) ≤
        C*AddCircle.haarAddCircle.real B := by
    rw [haarAddCircle_one_eq_volume]
    exact (phasePairLaw_marginal_fst hab hc B hB).trans
      (mul_le_mul_of_nonneg_right hCc ENNReal.toReal_nonneg)
  have hsnd (B : Set CircleX) (hB : MeasurableSet B) :
      (phasePairLaw a b c d).real (Prod.snd ⁻¹' B) ≤
        C*AddCircle.haarAddCircle.real B := by
    rw [haarAddCircle_one_eq_volume]
    exact (phasePairLaw_marginal_snd hab hd B hB).trans
      (mul_le_mul_of_nonneg_right hCd ENNReal.toReal_nonneg)
  have hmom (v w : ℤ) (hv : |v| < H) (hw : |w| < H) (hne : ¬(v=0 ∧ w=0)) :
      ‖∫ z, doubleFourier v w z ∂phasePairLaw a b c d‖ ≤
        1/(Real.pi*R*(b-a)) := by
    have hfpos : 0 < |(v : ℝ)*c+(w : ℝ)*d| := hR.trans_le (hsep v w hv hw hne)
    exact (phasePairLaw_fourier_bound hab v w (abs_pos.mp hfpos)).trans
      (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsep v w hv hw hne)
          Real.pi_pos.le) (sub_nonneg.mpr hab.le)))
  have h := arc_rectangle_discrepancy hH hδ x y r s (phasePairLaw a b c d)
    hC0 hε hfst hsnd hmom
  rw [haarAddCircle_one_eq_volume] at h
  simpa only [mul_one_div] using h

end Sampling
end ContinuousCircleWeight

end

end OAI
