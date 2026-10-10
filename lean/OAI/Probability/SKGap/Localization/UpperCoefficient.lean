import Mathlib
import OAI.Probability.SKGap.Localization.Magnetization

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace SKGapCutoff

noncomputable def upperCoefficient {n : ℕ} (x : Spin n) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then spin x p.1 * spin x p.2 else 0

lemma energy_sampled {n : ℕ} (g : GaussianCoordinates n) (x : Spin n) :
    energy (sampledInteraction g) x = ∑ p, upperCoefficient x p * g p := by
  have hp (i j : Fin n) :
      spin x i * sampledInteraction g i j * spin x j =
      upperCoefficient x (i,j) * g (i,j) + upperCoefficient x (j,i) * g (j,i) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [sampledInteraction, upperCoefficient, ne_of_lt h, h,
        not_lt_of_ge (le_of_lt h), min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]
      ring
    · subst j
      simp [sampledInteraction, upperCoefficient]
    · simp [sampledInteraction, upperCoefficient, ne_of_gt h, h,
        not_lt_of_ge (le_of_lt h), min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]
      ring
  unfold energy
  simp_rw [hp]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => upperCoefficient x (j, i) * g (j, i))]
  ring

lemma integral_exp_gaussian_linear {ι : Type*} [Fintype ι] (v : ℝ≥0) (a : ι → ℝ) :
    (∫ g : ι → ℝ, Real.exp (∑ p, a p * g p)
      ∂Measure.pi (fun _ => gaussianReal 0 v)) =
      Real.exp (v * (∑ p, a p ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun p z => Real.exp (a p * z))]
  have h (p : ι) : (∫ z : ℝ, Real.exp (a p * z) ∂gaussianReal 0 v) =
      Real.exp (v * a p ^ 2 / 2) := by
    have he := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) (a p)
    simpa [mgf] using he
  simp_rw [h]
  rw [← Real.exp_sum]
  congr 1
  simp [Finset.mul_sum, Finset.sum_div]

lemma integrable_exp_gaussian_linear {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (a : ι → ℝ) :
    Integrable (fun g : ι → ℝ => Real.exp (∑ p, a p * g p))
      (Measure.pi (fun _ => gaussianReal 0 v)) := by
  simpa only [Real.exp_sum] using
    (Integrable.fintype_prod (fun p => integrable_exp_mul_gaussianReal (μ := 0) (v := v) (a p)))

lemma sum_upperCoefficient_sq {n : ℕ} (x : Spin n) :
    ∑ p, upperCoefficient x p ^ 2 = (n : ℝ) * (n - 1) / 2 := by
  have hp (i j : Fin n) : upperCoefficient x (i,j) ^ 2 +
      upperCoefficient x (j,i) ^ 2 = 1 - if i = j then 1 else 0 := by
    rcases lt_trichotomy i j with h | h | h
    · simp [upperCoefficient, h, not_lt_of_ge (le_of_lt h), ne_of_lt h,
        mul_pow, spin_sq]
    · subst j; simp [upperCoefficient]
    · simp [upperCoefficient, h, not_lt_of_ge (le_of_lt h), ne_of_gt h,
        mul_pow, spin_sq]
  have hs := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => hp i j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => upperCoefficient x (j,i) ^ 2)] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Fintype.sum_ite_eq, Finset.sum_const] at hs
  rw [Fintype.sum_prod_type]
  nlinarith

noncomputable def replicaOverlap {n : ℕ} (x y : Spin n) : ℝ :=
  ∑ i, spin x i * spin y i

lemma sum_upperCoefficient_mul {n : ℕ} (x y : Spin n) :
    ∑ p, upperCoefficient x p * upperCoefficient y p =
      (replicaOverlap x y ^ 2 - n) / 2 := by
  have hp (i j : Fin n) : upperCoefficient x (i,j) * upperCoefficient y (i,j) +
      upperCoefficient x (j,i) * upperCoefficient y (j,i) =
      (spin x i * spin y i) * (spin x j * spin y j) - if i = j then 1 else 0 := by
    rcases lt_trichotomy i j with h | h | h
    · simp [upperCoefficient, h, not_lt_of_ge (le_of_lt h), ne_of_lt h]
      ring
    · subst j
      simp [upperCoefficient, mul_pow, ← sq, spin_sq]
    · simp [upperCoefficient, h, not_lt_of_ge (le_of_lt h), ne_of_gt h]
      ring
  have hs := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => hp i j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => upperCoefficient x (j,i) * upperCoefficient y (j,i))] at hs
  simp only [Fintype.sum_ite_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hs
  rw [Fintype.sum_prod_type]
  unfold replicaOverlap
  nlinarith

lemma integrable_exp_energy_sampled (β : ℝ) {n : ℕ} (x : Spin n) :
    Integrable (fun g => Real.exp (energy (sampledInteraction g) x)) (disorderLaw β n) := by
  simp_rw [energy_sampled]
  exact integrable_exp_gaussian_linear _ _

lemma integral_exp_energy_sampled (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    (∫ g, Real.exp (energy (sampledInteraction g) x) ∂disorderLaw β n) =
      Real.exp (β ^ 2 * (n - 1) / 4) := by
  simp_rw [energy_sampled]
  unfold disorderLaw
  rw [integral_exp_gaussian_linear _ (upperCoefficient x), sum_upperCoefficient_sq]
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp
  ring

lemma integrable_partition_sampled (β : ℝ) (n : ℕ) :
    Integrable (fun g => partition (sampledInteraction g)) (disorderLaw β n) := by
  exact integrable_finsetSum _ (fun x _ => integrable_exp_energy_sampled β x)

lemma integral_partition_sampled (β : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, partition (sampledInteraction g) ∂disorderLaw β n) =
      (2 : ℝ) ^ n * Real.exp (β ^ 2 * (n - 1) / 4) := by
  unfold partition
  rw [integral_finsetSum _ (fun x _ => integrable_exp_energy_sampled β x)]
  simp only [integral_exp_energy_sampled β hn, Finset.sum_const, Finset.card_univ,
    card_spin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

lemma sum_upperCoefficient_add_sq {n : ℕ} (x y : Spin n) :
    ∑ p, (upperCoefficient x p + upperCoefficient y p) ^ 2 =
      (n : ℝ) ^ 2 - 2 * n + replicaOverlap x y ^ 2 := by
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, sum_upperCoefficient_sq,
    sum_upperCoefficient_mul]
  ring

lemma combined_energy_sampled {n : ℕ} (g : GaussianCoordinates n) (x y : Spin n) :
    energy (sampledInteraction g) x + energy (sampledInteraction g) y =
      ∑ p, (upperCoefficient x p + upperCoefficient y p) * g p := by
  simp [energy_sampled, add_mul, Finset.sum_add_distrib]

lemma integrable_exp_combined_energy (β : ℝ) {n : ℕ} (x y : Spin n) :
    Integrable (fun g => Real.exp (energy (sampledInteraction g) x +
      energy (sampledInteraction g) y)) (disorderLaw β n) := by
  simp_rw [combined_energy_sampled]
  exact integrable_exp_gaussian_linear _ _

lemma integral_exp_combined_energy (β : ℝ) {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    (∫ g, Real.exp (energy (sampledInteraction g) x + energy (sampledInteraction g) y)
      ∂disorderLaw β n) =
      Real.exp (β ^ 2 * (n - 2) / 2 + β ^ 2 * replicaOverlap x y ^ 2 / (2 * n)) := by
  simp_rw [combined_energy_sampled]
  unfold disorderLaw
  rw [integral_exp_gaussian_linear _ (fun p => upperCoefficient x p + upperCoefficient y p),
    sum_upperCoefficient_add_sq]
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

lemma partition_sq_eq_sum {n : ℕ} (J : Interaction n) :
    partition J ^ 2 = ∑ x, ∑ y, Real.exp (energy J x + energy J y) := by
  simp [partition, pow_two, Real.exp_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma integrable_partition_sq_sampled (β : ℝ) (n : ℕ) :
    Integrable (fun g => partition (sampledInteraction g) ^ 2) (disorderLaw β n) := by
  simp_rw [partition_sq_eq_sum]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun y _ => integrable_exp_combined_energy β x y))

lemma integral_partition_sq_sampled (β : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, partition (sampledInteraction g) ^ 2 ∂disorderLaw β n) =
      Real.exp (β ^ 2 * (n - 2) / 2) *
        ∑ x : Spin n, ∑ y : Spin n, Real.exp (β ^ 2 * replicaOverlap x y ^ 2 / (2 * n)) := by
  simp_rw [partition_sq_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun y _ => integrable_exp_combined_energy β x y))]
  simp_rw [integral_finsetSum _ (fun y _ => integrable_exp_combined_energy β _ y),
    integral_exp_combined_energy β hn, Real.exp_add, ← Finset.mul_sum]

def multiplySpin {n : ℕ} (x y : Spin n) : Spin n := fun i => if x i then y i else !(y i)

@[simp] lemma spin_multiplySpin {n : ℕ} (x y : Spin n) (i : Fin n) :
    spin (multiplySpin x y) i = spin x i * spin y i := by
  cases hx : x i <;> cases hy : y i <;> simp [spin, multiplySpin, hx, hy]

@[simp] lemma multiplySpin_self {n : ℕ} (x y : Spin n) :
    multiplySpin x (multiplySpin x y) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [multiplySpin, hx, hy]

def multiplySpinEquiv {n : ℕ} (x : Spin n) : Spin n ≃ Spin n where
  toFun := multiplySpin x
  invFun := multiplySpin x
  left_inv := multiplySpin_self x
  right_inv := multiplySpin_self x

lemma replicaOverlap_eq_magnetization {n : ℕ} (x y : Spin n) :
    replicaOverlap x y = magnetization (multiplySpin x y) := by
  simp [replicaOverlap, magnetization]

lemma sum_replicaOverlap {n : ℕ} (x : Spin n) (f : ℝ → ℝ) :
    ∑ y, f (replicaOverlap x y) = ∑ y : Spin n, f (magnetization y) := by
  simp_rw [replicaOverlap_eq_magnetization]
  exact (multiplySpinEquiv x).sum_comp (fun y => f (magnetization y))

lemma partition_second_moment_identity (β : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, partition (sampledInteraction g) ^ 2 ∂disorderLaw β n) /
      (∫ g, partition (sampledInteraction g) ∂disorderLaw β n) ^ 2 =
    Real.exp (-β ^ 2 / 2) *
      ((∑ x : Spin n, Real.exp (β ^ 2 * magnetization x ^ 2 / (2 * n))) / (2 : ℝ) ^ n) := by
  rw [integral_partition_sq_sampled β hn, integral_partition_sampled β hn]
  simp_rw [sum_replicaOverlap _ (fun z => Real.exp (β ^ 2 * z ^ 2 / (2 * n)))]
  simp only [Finset.sum_const, Finset.card_univ, card_spin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  have he : Real.exp (β ^ 2 * (n - 2) / 2) =
      Real.exp (-β ^ 2 / 2) * Real.exp (β ^ 2 * (n - 1) / 4) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp

lemma integral_exp_gaussian_quadratic {a : ℝ} (ha : a < 1) :
    (∫ z : ℝ, Real.exp (a * z ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (z : ℝ) : gaussianPDFReal 0 1 z * Real.exp (a * z ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - a) / 2) * z ^ 2) := by
    simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he]
  rw [integral_const_mul, integral_gaussian]
  have hd : Real.pi / ((1 - a) / 2) = (2 * Real.pi) / (1 - a) := by
    field_simp [ne_of_gt (sub_pos.mpr ha)]
  rw [hd, Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hπ : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

lemma integrable_exp_gaussian_quadratic {a : ℝ} (ha : a < 1) :
    Integrable (fun z : ℝ => Real.exp (a * z ^ 2 / 2)) (gaussianReal 0 1) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_exp_gaussian_quadratic ha] at hz
  exact (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by linarith)))) hz

lemma sign_sum_exponential (n : ℕ) (t : ℝ) :
    ∑ x : Spin n, Real.exp (t * magnetization x) = (2 * Real.cosh t) ^ n := by
  simp_rw [magnetization, Finset.mul_sum, Real.exp_sum]
  have he : (∑ x : Spin n, ∏ i, Real.exp (t * spin x i)) =
      ∏ i : Fin n, ∑ b : Bool, Real.exp (t * if b then 1 else -1) := by
    exact (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) =>
      Real.exp (t * if b then 1 else -1))).symm
  rw [he]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, mul_neg_one, mul_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Real.cosh_eq]
  ring

lemma gaussian_sign_square_identity (β : ℝ) {n : ℕ} (x : Spin n) :
    (∫ z : ℝ, Real.exp ((β * magnetization x / Real.sqrt n) * z) ∂gaussianReal 0 1) =
      Real.exp (β ^ 2 * magnetization x ^ 2 / (2 * n)) := by
  have he := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
    (β * magnetization x / Real.sqrt n)
  simp only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] at he
  rw [he]
  congr 1
  rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

lemma cosh_scaled_pow_le (β z : ℝ) {n : ℕ} (hn : 0 < n) :
    Real.cosh (β * z / Real.sqrt n) ^ n ≤ Real.exp (β ^ 2 * z ^ 2 / 2) := by
  calc
    _ ≤ (Real.exp ((β * z / Real.sqrt n) ^ 2 / 2)) ^ n :=
      pow_le_pow_left₀ (le_of_lt (Real.cosh_pos _)) (Real.cosh_le_exp_half_sq _) n
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      field_simp

lemma sign_square_moment_le (β : ℝ) (hβ : β ^ 2 < 1) {n : ℕ} (hn : 0 < n) :
    (∑ x : Spin n, Real.exp (β ^ 2 * magnetization x ^ 2 / (2 * n))) / (2 : ℝ) ^ n ≤
      (Real.sqrt (1 - β ^ 2))⁻¹ := by
  let f : ℝ → ℝ := fun z =>
    (∑ x : Spin n, Real.exp ((β * magnetization x / Real.sqrt n) * z)) / (2 : ℝ) ^ n
  have hf : Integrable f (gaussianReal 0 1) :=
    (integrable_finsetSum _ (fun x _ => integrable_exp_mul_gaussianReal
      (μ := 0) (v := 1) (β * magnetization x / Real.sqrt n))).div_const _
  have hid (z : ℝ) : f z = Real.cosh (β * z / Real.sqrt n) ^ n := by
    dsimp [f]
    have he (x : Spin n) : (β * magnetization x / Real.sqrt n) * z =
        (β * z / Real.sqrt n) * magnetization x := by ring
    simp_rw [he]
    rw [sign_sum_exponential, mul_pow]
    field_simp
  have hle := integral_mono hf (integrable_exp_gaussian_quadratic hβ)
    (fun z => by rw [hid]; exact cosh_scaled_pow_le β z hn)
  rw [integral_exp_gaussian_quadratic hβ] at hle
  dsimp [f] at hle
  rw [integral_div, integral_finsetSum _ (fun x _ =>
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1)
      (β * magnetization x / Real.sqrt n))] at hle
  simpa only [gaussian_sign_square_identity] using hle

lemma partition_second_moment_bound (β : ℝ) (hβ : β ^ 2 < 1) {n : ℕ} (hn : 0 < n) :
    (∫ g, partition (sampledInteraction g) ^ 2 ∂disorderLaw β n) /
      (∫ g, partition (sampledInteraction g) ∂disorderLaw β n) ^ 2 ≤
      (Real.sqrt (1 - β ^ 2))⁻¹ := by
  rw [partition_second_moment_identity β hn]
  have hm := sign_square_moment_le β hβ hn
  have he : Real.exp (-β ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg β])
  calc
    _ ≤ Real.exp (-β ^ 2 / 2) * (Real.sqrt (1 - β ^ 2))⁻¹ :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (Real.sqrt (1 - β ^ 2))⁻¹)

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

end

end OAI
