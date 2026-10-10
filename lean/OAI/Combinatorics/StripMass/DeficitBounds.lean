import Mathlib
import OAI.Combinatorics.StripMass.Basic

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
section GramBounds
open Set MeasureTheory
theorem expected_deficit_bounds (N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - expectation N (reflectionProduct N x) ∧
      1 - expectation N (reflectionProduct N x) ≤
        Real.sqrt x * expectation N (inverseHalfSum N) := by
  rw [← expectation_deficit N hx.le]
  constructor
  · apply expectation_nonneg
    intro y hy
    exact sub_nonneg.2 ((le_abs_self _).trans (abs_reflectionProduct_le_one hy hx.le))
  · have hi := integral_mono_ae (integrableOn_deficit_density N hx.le)
        ((integrableOn_inverseHalfSum_density N).const_mul (Real.sqrt x)) (by
          filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
          have hp := (le_abs_self (1 - reflectionProduct N x y)).trans (reflectionProduct_endpoint_bound hy hx)
          exact (mul_le_mul_of_nonneg_right hp (density_pos hy).le).trans_eq (mul_assoc _ _ _))
    unfold expectation
    rw [← mul_div_assoc, ← integral_const_mul]
    exact div_le_div_of_nonneg_right hi (normalizer_pos N).le

theorem measurable_momentIntegrand (N : ℕ) : Measurable (momentIntegrand N) := by
  have hm : StronglyMeasurable (Function.uncurry
      (fun x (y : Fin N → ℝ) => reflectionProduct N x y * density N y)) := by
    exact ((measurable_reflectionProduct N).mul ((measurable_density N).comp measurable_snd)).stronglyMeasurable
  have hi := hm.integral_prod_right (ν := volume.restrict (orderedDomain N))
  exact ((measurable_const.sub (hi.measurable.div_const (normalizer N))).mul measurable_omega).div measurable_id

theorem momentIntegrand_bounds (N : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ momentIntegrand N x ∧ momentIntegrand N x ≤
      expectation N (inverseHalfSum N) * x ^ (-(3 / 4 : ℝ)) := by
  have hb := expected_deficit_bounds N hx.1
  have hE : 0 ≤ expectation N (inverseHalfSum N) := by
    apply expectation_nonneg
    intro y hy
    exact Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hy.2 i).1 _).le
  constructor
  · exact div_nonneg (mul_nonneg hb.1 (omega_nonneg x)) hx.1.le
  · have hpow : Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x = x ^ (-(3 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx.1]
      calc
        x ^ (1 / 2 + -(1 / 4) : ℝ) / x = x ^ (1 / 4 : ℝ) / x ^ (1 : ℝ) := by norm_num
        _ = x ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hx.1 _ _).symm
        _ = _ := by norm_num
    calc
      momentIntegrand N x ≤ (Real.sqrt x * expectation N (inverseHalfSum N)) * omega x / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb.2 (omega_nonneg x)) hx.1.le
      _ ≤ (Real.sqrt x * expectation N (inverseHalfSum N)) * x ^ (-(1 / 4 : ℝ)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (omega_le_rpow hx)
          (mul_nonneg (Real.sqrt_nonneg x) hE)) hx.1.le
      _ = expectation N (inverseHalfSum N) * (Real.sqrt x * x ^ (-(1 / 4 : ℝ)) / x) := by ring
      _ = _ := by rw [hpow]

 
theorem integrableOn_momentIntegrand (N : ℕ) :
    IntegrableOn (momentIntegrand N) (Ioo 0 1) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  apply (hp.const_mul (expectation N (inverseHalfSum N))).mono'
    (measurable_momentIntegrand N).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (momentIntegrand_bounds N hx).1]
  exact (momentIntegrand_bounds N hx).2

end GramBounds

section CauchyAlternants
open Matrix

 
def cauchyMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => 1 / (x i + y j)

theorem det_cauchyMatrix_pos {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < (cauchyMatrix x y).det := by
  induction n with
  | zero => simp [Matrix.det_isEmpty]
  | succ n ih =>
    let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := cauchyMatrix x y
    let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
      Matrix.of fun i j => if i = 0 then A i j else A i j - (x 0 + y 0) / (x i + y 0) * A 0 j
    have hAB : A.det = B.det := by
      apply Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i = 0 then 0 else (x 0 + y 0) / (x i + y 0)) 0
      · simp
      · intro i j
        by_cases hi : i = 0
        · simp [hi, B]
        · simp only [B, Matrix.of_apply, hi, ite_false, ite_true]
          ring
    have hB0 (i : Fin n) : B i.succ 0 = 0 := by
      simp only [B, Matrix.of_apply, Fin.succ_ne_zero, ite_false, A, cauchyMatrix]
      have hsum (i j) : x i + y j ≠ 0 := (add_pos (hx0 i) (hy0 j)).ne'
      field_simp [hsum]
      ring
    let r : Fin n → ℝ := fun i => (x i.succ - x 0) / (x i.succ + y 0)
    let s : Fin n → ℝ := fun j => (y j.succ - y 0) / (x 0 + y j.succ)
    have htail : B.submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin n => r i * (s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)) := by
      apply Matrix.ext
      intro i j
      change 1 / (x i.succ + y j.succ) -
        (x 0 + y 0) / (x i.succ + y 0) * (1 / (x 0 + y j.succ)) =
        ((x i.succ - x 0) / (x i.succ + y 0)) *
          (((y j.succ - y 0) / (x 0 + y j.succ)) * (1 / (x i.succ + y j.succ)))
      have hsum (i j) : x i + y j ≠ 0 := (add_pos (hx0 i) (hy0 j)).ne'
      field_simp [hsum]
      ring
    have hdetB : B.det = A 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      simp [hB0, show B 0 0 = A 0 0 by simp [B]]
    have hscale : (Matrix.of (fun i j : Fin n => r i * (s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j))).det =
        (∏ i, r i) * ((∏ j, s j) * (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det) := by
      calc
        _ = (∏ i, r i) * (Matrix.of (fun i j => s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)).det := by
          simpa only [Matrix.of_apply] using Matrix.det_mul_column r
            (Matrix.of fun i j => s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)
        _ = _ := by rw [Matrix.det_mul_row]
    change 0 < A.det
    rw [hAB, hdetB, htail, hscale]
    apply mul_pos
    · exact one_div_pos.2 (add_pos (hx0 _) (hy0 _))
    · apply mul_pos
      · exact Finset.prod_pos fun i _ => div_pos (sub_pos.2 (hx (Fin.succ_pos i))) (add_pos (hx0 _) (hy0 _))
      · apply mul_pos
        · exact Finset.prod_pos fun i _ => div_pos (sub_pos.2 (hy (Fin.succ_pos i))) (add_pos (hx0 _) (hy0 _))
        · exact ih _ _ (hx.comp (Fin.strictMono_succ)) (hy.comp (Fin.strictMono_succ))
            (fun i => hx0 i.succ) (fun i => hy0 i.succ)

theorem det_vandermonde_pos {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) :
    0 < (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.2 (hx (Finset.mem_Ioi.1 hj))

def cauchyAlternant {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (Matrix.vandermonde x).det * (cauchyMatrix x y).det * (Matrix.vandermonde y).det

 theorem cauchyAlternant_pos {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < cauchyAlternant x y :=
  mul_pos (mul_pos (det_vandermonde_pos x hx) (det_cauchyMatrix_pos x y hx hy hx0 hy0))
    (det_vandermonde_pos y hy)

 theorem cauchyAlternant_permute {n : ℕ} (x y : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) :
    cauchyAlternant (x ∘ σ) (y ∘ τ) = cauchyAlternant x y := by
  have hV (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
      (Matrix.vandermonde (v ∘ p)).det = (p.sign : ℝ) * (Matrix.vandermonde v).det := by
    have heq : Matrix.vandermonde (v ∘ p) = (Matrix.vandermonde v).submatrix p id := rfl
    rw [heq, Matrix.det_permute]
  have hC : cauchyMatrix (x ∘ σ) (y ∘ τ) = (cauchyMatrix x y).submatrix σ τ := rfl
  unfold cauchyAlternant
  rw [hV, hV, hC]
  have hCdet : ((cauchyMatrix x y).submatrix σ τ).det =
      (σ.sign : ℝ) * ((τ.sign : ℝ) * (cauchyMatrix x y).det) := by
    have heq : (cauchyMatrix x y).submatrix σ τ =
      ((cauchyMatrix x y).submatrix id τ).submatrix σ id := rfl
    rw [heq, Matrix.det_permute, Matrix.det_permute']
  rw [hCdet]
  have hs (p : Equiv.Perm (Fin n)) : (p.sign : ℝ) * (p.sign : ℝ) = 1 := by
    norm_cast
    simp [Int.units_mul_self]
  calc
    _ = ((σ.sign : ℝ) * (σ.sign : ℝ)) * ((τ.sign : ℝ) * (τ.sign : ℝ)) *
      ((Matrix.vandermonde x).det * (cauchyMatrix x y).det * (Matrix.vandermonde y).det) := by ring
    _ = _ := by rw [hs, hs]; ring

 theorem cauchyAlternant_nonneg {n : ℕ} (x y : Fin n → ℝ)
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) : 0 ≤ cauchyAlternant x y := by
  by_cases hx : Function.Injective x
  · by_cases hy : Function.Injective y
    · have hxs : StrictMono (x ∘ Tuple.sort x) :=
        (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
      have hys : StrictMono (y ∘ Tuple.sort y) :=
        (Tuple.monotone_sort y).strictMono_of_injective (hy.comp (Tuple.sort y).injective)
      rw [← cauchyAlternant_permute x y (Tuple.sort x) (Tuple.sort y)]
      exact (cauchyAlternant_pos _ _ hxs hys (fun i => hx0 _) (fun i => hy0 _)).le
    · have hz : (Matrix.vandermonde y).det = 0 := by
        by_contra h
        exact hy (Matrix.det_vandermonde_ne_zero_iff.1 h)
      simp [cauchyAlternant, hz]
  · have hz : (Matrix.vandermonde x).det = 0 := by
      by_contra h
      exact hx (Matrix.det_vandermonde_ne_zero_iff.1 h)
    simp [cauchyAlternant, hz]

end CauchyAlternants

section DeterminantIntegration
open MeasureTheory Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

 theorem integrable_det_columns (F : n → n → α → ℝ)
    (hF : ∀ i j, Integrable (F i j) μ) :
    Integrable (fun x : n → α => (Matrix.of fun i j => F i j (x j)).det) (Measure.pi fun _ => μ) := by
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod fun j => hF (σ j) j).const_mul _

 theorem integral_det_columns (F : n → n → α → ℝ)
    (hF : ∀ i j, Integrable (F i j) μ) :
    (∫ x : n → α, (Matrix.of fun i j => F i j (x j)).det ∂Measure.pi (fun _ => μ)) =
      (Matrix.of fun i j => ∫ t, F i j t ∂μ).det := by
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_const_mul, integral_fintype_prod_eq_prod]
  · intro σ _
    exact (Integrable.fintype_prod fun j => hF (σ j) j).const_mul _

theorem integrable_det_mul_det (f g : n → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : n → α => (Matrix.of fun i j => f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det) (Measure.pi fun _ => μ) := by
  classical
  let H : Equiv.Perm n → (n → α) → ℝ := fun σ x =>
    (Matrix.of fun i j => f (σ j) (x j) * g i (x j)).det
  have hH (σ : Equiv.Perm n) : Integrable (H σ) (Measure.pi fun _ => μ) := by
    exact integrable_det_columns (fun i j t => f (σ j) t * g i t) (fun i j => hfg _ _)
  have hexpand (x : n → α) :
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * H σ x := by
    rw [Matrix.det_apply', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [H]
    have hscale := Matrix.det_mul_row (fun j => f (σ j) (x j))
      (Matrix.of fun i j => g i (x j))
    simp only [Matrix.of_apply] at hscale
    rw [hscale, mul_assoc]
  simp_rw [hexpand]
  exact integrable_finsetSum _ fun σ _ => (hH σ).const_mul _

 

theorem integral_det_mul_det (f g : n → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : n → α, (Matrix.of fun i j => f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det ∂Measure.pi (fun _ => μ)) =
      (Fintype.card (Equiv.Perm n) : ℝ) *
        (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
  classical
  let H : Equiv.Perm n → (n → α) → ℝ := fun σ x =>
    (Matrix.of fun i j => f (σ j) (x j) * g i (x j)).det
  have hH (σ : Equiv.Perm n) : Integrable (H σ) (Measure.pi fun _ => μ) := by
    exact integrable_det_columns (fun i j t => f (σ j) t * g i t) (fun i j => hfg _ _)
  have hexpand (x : n → α) :
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * H σ x := by
    rw [Matrix.det_apply', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [H]
    have hscale := Matrix.det_mul_row (fun j => f (σ j) (x j))
      (Matrix.of fun i j => g i (x j))
    simp only [Matrix.of_apply] at hscale
    rw [hscale, mul_assoc]
  have hI (σ : Equiv.Perm n) :
      (∫ x, H σ x ∂Measure.pi (fun _ => μ)) =
      (Equiv.Perm.sign σ : ℝ) * (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
    rw [integral_det_columns _ (fun i j => hfg (σ j) i)]
    have hmat : (Matrix.of fun i j => ∫ t, f (σ j) t * g i t ∂μ) =
        (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).transpose.submatrix id σ := rfl
    rw [hmat, Matrix.det_permute', Matrix.det_transpose]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun σ _ => (hH σ).const_mul _)]
  simp_rw [integral_const_mul, hI, ← mul_assoc]
  have hsign (σ : Equiv.Perm n) : (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ) = 1 := by
    norm_cast
    simp [Int.units_mul_self]
  simp_rw [hsign, one_mul]
  simp

end DeterminantIntegration

open Set MeasureTheory Matrix

 

def boundedCauchy (x y : ℝ) : ℝ := x / (x + y)
def momentBasis (k : ℕ) (x : ℝ) : ℝ := x ^ k * omega x
def transformedBasis (k : ℕ) (x : ℝ) : ℝ :=
  ∫ y in Ioo (0 : ℝ) 1, boundedCauchy x y * momentBasis k y

def momentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∫ x in Ioo (0 : ℝ) 1, momentBasis i.val x * transformedBasis j.val x

theorem momentBasis_bounds (k : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ momentBasis k x ∧ momentBasis k x ≤ omega x := by
  constructor
  · exact mul_nonneg (pow_nonneg hx.1.le _) (omega_nonneg _)
  · exact mul_le_of_le_one_left (omega_nonneg _) (pow_le_one₀ hx.1.le hx.2.le)

theorem measurable_momentBasis (k : ℕ) : Measurable (momentBasis k) :=
  (measurable_id.pow_const k).mul measurable_omega

theorem integrableOn_momentBasis (k : ℕ) : IntegrableOn (momentBasis k) (Ioo 0 1) := by
  apply integrableOn_omega.mono' (measurable_momentBasis k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (momentBasis_bounds k hx).1] using
    (momentBasis_bounds k hx).2

theorem boundedCauchy_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < boundedCauchy x y ∧ boundedCauchy x y ≤ 1 := by
  constructor
  · exact div_pos hx (add_pos hx hy)
  · exact (div_le_one (add_pos hx hy)).2 (by linarith)

theorem integrableOn_boundedCauchy_basis (k : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => boundedCauchy x y * momentBasis k y) (Ioo 0 1) := by
  have hm : Measurable (fun y => boundedCauchy x y * momentBasis k y) := by
    exact ((measurable_const.div (measurable_const.add measurable_id))).mul (measurable_momentBasis k)
  apply (integrableOn_momentBasis k).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hk := boundedCauchy_bounds hx hy.1
  have hb := momentBasis_bounds k hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.1.le hb.1)]
  exact mul_le_of_le_one_left hb.1 hk.2

theorem transformedBasis_bounds (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ transformedBasis k x ∧ transformedBasis k x ≤ ∫ y in Ioo (0 : ℝ) 1, omega y := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (boundedCauchy_bounds hx hy.1).1.le (momentBasis_bounds k hy).1
  · apply integral_mono_ae (integrableOn_boundedCauchy_basis k hx) integrableOn_omega
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (mul_le_of_le_one_left (momentBasis_bounds k hy).1
      (boundedCauchy_bounds hx hy.1).2).trans (momentBasis_bounds k hy).2

theorem measurable_transformedBasis (k : ℕ) : Measurable (transformedBasis k) := by
  have hm : StronglyMeasurable (Function.uncurry (fun x y => boundedCauchy x y * momentBasis k y)) := by
    exact ((measurable_fst.div (measurable_fst.add measurable_snd)).mul
      ((measurable_momentBasis k).comp measurable_snd)).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

theorem integrableOn_basis_transformedBasis (i j : ℕ) :
    IntegrableOn (fun x => momentBasis i x * transformedBasis j x) (Ioo 0 1) := by
  apply (integrableOn_omega.mul_const (∫ y in Ioo (0 : ℝ) 1, omega y)).mono'
    ((measurable_momentBasis i).mul (measurable_transformedBasis j)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := momentBasis_bounds i hx
  have ht := transformedBasis_bounds j hx.1
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 ht.1)]
  exact mul_le_mul hb.2 ht.2 ht.1 (omega_nonneg _)

def basisDet (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (Matrix.of fun i j : Fin N => momentBasis i.val (x j)).det

def transformedDet (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).det

end
end CriticalStrip

end OAI
