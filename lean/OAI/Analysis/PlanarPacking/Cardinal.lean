import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def b : ℝ := Real.sqrt 3 / 2
noncomputable def h : ℝ := 2 / 5
noncomputable def B : ℝ := 4 / 3

def residues : Finset ℕ := {0, 1, 3, 4, 7, 9}


abbrev Node := {n : ℕ // 0 < n ∧ n % 12 ∈ residues}


abbrev X := lp (fun _ : Node × Bool => ℝ) 1

noncomputable def P (s : ℝ) : ℝ :=
  ∏ a ∈ residues, (2 * Real.sin (Real.pi * (s - a) / 12)) ^ 2

noncomputable def Pcoeff : ℕ → ℂ
  | 0 => 5
  | 1 => -1 + 2 * Complex.I * b
  | 2 => 1 + 2 * Complex.I * b
  | 3 => -2
  | 4 => -(1 / 2) + Complex.I * b
  | 5 => -1 - 2 * Complex.I * b
  | 6 => 1
  | _ => 0

noncomputable def Q (n : ℕ) : ℝ :=
  (Real.pi / 6) ^ 2 * ∏ a ∈ residues.erase (n % 12),
    (2 * Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12)) ^ 2

noncomputable def D (n : ℕ) : ℝ :=
  (Real.pi / 6) * ∑ a ∈ residues.erase (n % 12),
    (Real.cos (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12) /
      Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12))

noncomputable def lambda (t : ℝ) : ℂ :=
  Complex.I / ((b : ℂ) * ((t : ℂ) + Complex.I * (h : ℂ)))
noncomputable def z (t : ℝ) : ℂ :=
  -(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ)) - Complex.I * (h : ℂ)


noncomputable def u (n j : ℕ) (t : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) ^ 2 * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ) / 6 - t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

noncomputable def v (n j : ℕ) (t : ℝ) : ℂ :=
  2 * Complex.I * Real.pi * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

structure CardinalData where
  C : ℝ
  c₀ : ℝ
  d₀ : ℝ
  x : X

noncomputable def density (p : CardinalData) (j : ℕ) (t : ℝ) : ℂ :=
  (p.c₀ : ℂ) * u 0 j t + (p.d₀ : ℂ) * v 0 j t +
    ∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)


noncomputable def kernelMoment (ell : ℕ) (s t : ℝ) : ℂ :=
  lambda t * (Complex.I * Real.pi * z t) ^ ell *
    Complex.exp (Complex.I * Real.pi * z t * s)


noncomputable def K (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  ((p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
    ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ) / 6)) +
    ∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density p j t * kernelMoment ell s t).re

noncomputable def positiveData (x : X) : CardinalData := ⟨0, 0, 0, x⟩


noncomputable def Scoords (x : X) (ni : Node × Bool) : ℝ :=
  if ni.2 then
    (D ni.1.val * K (positiveData x) 0 ni.1.val - K (positiveData x) 1 ni.1.val) /
      Q ni.1.val
  else -K (positiveData x) 0 ni.1.val / Q ni.1.val

noncomputable def fixed₁ (x : X) : CardinalData := ⟨-13/1000, 1, 11/25, x⟩
noncomputable def fixed₂ (x : X) : CardinalData := ⟨17/1000, 0, -46/125, x⟩

theorem b_pos : 0 < b := by unfold b; positivity

theorem b_sq : b ^ 2 = 3 / 4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem B_eq_inv_b_sq : B = (b ^ 2)⁻¹ := by rw [b_sq]; norm_num [B]

theorem z_im (t : ℝ) : (z t).im = h * (B / (t ^ 2 + h ^ 2) - 1) := by
  simp [z, Complex.div_im, Complex.normSq, pow_two]
  ring

theorem strict_damping {t : ℝ} (ht : |t| ≤ 1) : (26 : ℝ) / 435 ≤ (z t).im := by
  rw [z_im]
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (abs_nonneg t) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using this.mpr ht
  have hd : 0 < t ^ 2 + h ^ 2 := by unfold h; positivity
  have hb : (4 : ℝ) / 3 / ((29 : ℝ) / 25) ≤ B / (t ^ 2 + h ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4/3) hd
    change t ^ 2 + (2/5 : ℝ) ^ 2 ≤ 29/25
    linarith
  unfold h at *
  norm_num at hb ⊢
  linarith



theorem X_summable (x : X) : Summable (fun ni : Node × Bool => |x ni|) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem X_summable_coord (x : X) (i : Bool) : Summable (fun n : Node => |x (n, i)|) := by
  exact (X_summable x).comp_injective (fun _ _ hh => congrArg Prod.fst hh)


theorem X_norm (x : X) : ‖x‖ = ∑' n : Node, (|x (n, false)| + |x (n, true)|) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs]
  rw [(X_summable x).tsum_prod]
  simp only [tsum_bool]

theorem X_summable_pairs (x : X) :
    Summable (fun n : Node => |x (n, false)| + |x (n, true)|) := by
  exact (X_summable_coord x false).add (X_summable_coord x true)


theorem h_pos : 0 < h := by norm_num [h]
theorem B_pos : 0 < B := by norm_num [B]

theorem imaginary_gaussian_denominator (t : ℝ) :
    h ≤ ‖(t : ℂ) + Complex.I * (h : ℂ)‖ := by
  have hh := Complex.abs_im_le_norm ((t : ℂ) + Complex.I * (h : ℂ))
  simpa [abs_of_pos h_pos] using hh

theorem lambda_bound (t : ℝ) : ‖lambda t‖ ≤ 1 / (b * h) := by
  rw [lambda, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos b_pos]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos b_pos h_pos)
  exact mul_le_mul_of_nonneg_left (imaginary_gaussian_denominator t) b_pos.le

theorem z_bound (t : ℝ) : ‖z t‖ ≤ B / h + h := by
  have hden : 0 < ‖(t : ℂ) + Complex.I * (h : ℂ)‖ :=
    h_pos.trans_le (imaginary_gaussian_denominator t)
  calc
    ‖z t‖ ≤ ‖-(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ))‖ +
      ‖Complex.I * (h : ℂ)‖ := norm_sub_le _ _
    _ = B / ‖(t : ℂ) + Complex.I * (h : ℂ)‖ + h := by
      simp [Complex.norm_real, abs_of_pos B_pos, abs_of_pos h_pos]
    _ ≤ B / h + h := add_le_add
      (div_le_div_of_nonneg_left B_pos.le h_pos (imaginary_gaussian_denominator t)) le_rfl

noncomputable def kappa : ℝ := 26 * Real.pi / 435

theorem kappa_pos : 0 < kappa := by unfold kappa; positivity


theorem kernelMoment_bound (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : |t| ≤ 1) :
    ‖kernelMoment ell s t‖ ≤ (1 / (b*h)) * (Real.pi * (B/h+h))^ell *
      Real.exp (-kappa*s) := by
  have hex : ‖Complex.exp (Complex.I * Real.pi * z t * s)‖ ≤
      Real.exp (-kappa*s) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_sub,
      sub_zero, zero_add]
    have hd := strict_damping ht
    dsimp [kappa]
    nlinarith [mul_nonneg Real.pi_pos.le hs]
  unfold kernelMoment
  rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have hb' := b_pos
  have hh' := h_pos
  have hB' := B_pos
  have hl := lambda_bound t
  have hz := z_bound t
  gcongr


def coeffMass : ℕ → ℝ
  | 0 => 5
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | _ => 0

theorem Pcoeff_norm (j : ℕ) : ‖Pcoeff j‖ = coeffMass j := by
  have hb := b_sq
  rcases lt_or_ge j 7 with hj | hj
  · interval_cases j <;>
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num [coeffMass])).mp
    all_goals
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Pcoeff, coeffMass, Complex.normSq]
    all_goals nlinarith [hb]
  · have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    simp [Pcoeff, coeffMass]


lemma positive_coeff_mass : ∑ l ∈ Finset.Icc 1 6, ‖Pcoeff l‖ = 10 := by
  simp only [Pcoeff_norm]
  norm_num [Finset.sum_Icc_succ_top, coeffMass]

lemma positive_coeff_mass_le (j : ℕ) : ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ ≤ 10 := by
  rw [← positive_coeff_mass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    omega
  · intro l _ _; exact norm_nonneg _

lemma phase_norm (n : ℕ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * Real.pi * t * n)‖ = 1 := by
  simp [Complex.norm_exp]

lemma atom_phase_norm (n l : ℕ) :
    ‖Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)‖ = 1 := by
  simp [Complex.norm_exp]

lemma frequency_distance_le {l : ℕ} (hl : l ≤ 6) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(l : ℂ)/6 - (t : ℂ)‖ ≤ 1 := by
  have he : (l : ℂ)/6 - (t : ℂ) = (((l : ℝ)/6 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hln : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlu : (l : ℝ) ≤ 6 := by exact_mod_cast hl
  constructor <;> linarith [ht.1, ht.2]


lemma u_bound (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖u n j t‖ ≤ 20 * Real.pi^2 := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul, norm_mul, atom_phase_norm, mul_one]
        exact (mul_le_mul_of_nonneg_right (frequency_distance_le (Finset.mem_Icc.mp hl).2 ht)
          (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ 10 := positive_coeff_mass_le j
  unfold u
  rw [norm_mul, norm_mul, norm_mul, norm_pow, phase_norm]
  simp only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [sq_nonneg Real.pi]

lemma v_bound (n j : ℕ) {t : ℝ} (_ : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ 20 * Real.pi := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul, atom_phase_norm, mul_one]
      _ ≤ 10 := positive_coeff_mass_le j
  unfold v
  rw [norm_mul, norm_mul, norm_mul, norm_mul, phase_norm]
  simp only [Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

noncomputable def densityBound : ℝ := 20 * Real.pi^2

lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma summand_bound (x : X) (n : Node) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t‖ ≤
      densityBound * (|x (n, false)| + |x (n, true)|) := by
  calc
    _ ≤ ‖(x (n, false) : ℂ) * u n.val j t‖ + ‖(x (n, true) : ℂ) * v n.val j t‖ := norm_add_le _ _
    _ = |x (n, false)| * ‖u n.val j t‖ + |x (n, true)| * ‖v n.val j t‖ := by
      simp [Complex.norm_real]
    _ ≤ |x (n, false)| * densityBound + |x (n, true)| * densityBound := by
      gcongr
      exacts [u_bound _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring

lemma density_summable (x : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun n : Node => (x (n, false) : ℂ) * u n.val j t +
      (x (n, true) : ℂ) * v n.val j t) := by
  exact ((X_summable_pairs x).mul_left densityBound).of_norm_bounded
    (fun n => summand_bound x n j ht)

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound p.x n j ht)
    exact (X_summable_pairs p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound p.x n j ht)
          ((X_summable_pairs p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


noncomputable def kernelEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  (1/(b*h)) * (Real.pi*(B/h+h))^ell * Real.exp (-kappa*s)

lemma kernelEnvelope_nonneg (ell : ℕ) (s : ℝ) : 0 ≤ kernelEnvelope ell s := by
  have := b_pos
  have := h_pos
  have := B_pos
  unfold kernelEnvelope
  positivity

lemma kernelMoment_bound' (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖kernelMoment ell s t‖ ≤ kernelEnvelope ell s := by
  apply kernelMoment_bound ell hs
  rw [abs_of_nonneg ht.1]
  exact ht.2

lemma atomic_bound (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      25 * kernelEnvelope ell s := by
  have hzero : ‖Pcoeff 0 * kernelMoment ell s 0‖ ≤ 5 * kernelEnvelope ell s := by
    rw [norm_mul, Pcoeff_norm]
    apply mul_le_mul_of_nonneg_left (kernelMoment_bound' ell hs (by simp)) (by norm_num [coeffMass])
  have hsum : ‖∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      20 * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 6, ‖2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 6, 2 * ‖Pcoeff j‖ * kernelEnvelope ell s := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
        apply kernelMoment_bound' ell hs
        have hju : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
        constructor
        · positivity
        · linarith
      _ = 20 * kernelEnvelope ell s := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, positive_coeff_mass]
        ring
  exact (norm_add_le _ _).trans (by linarith)

lemma piece_interval {j : ℕ} (hj : j < 6) {t : ℝ}
    (ht : t ∈ Set.uIcc ((j : ℝ)/6) (((j : ℝ)+1)/6)) : t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIcc_of_le (by linarith : (j : ℝ)/6 ≤ ((j : ℝ)+1)/6)] at ht
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast (show j ≤ 5 by omega)
  constructor <;> linarith [ht.1, ht.2]

lemma integral_piece_bound (p : CardinalData) (ell j : ℕ) (hj : j < 6)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => density p j t * kernelMoment ell s t)
    (a := (j : ℝ)/6) (b := ((j : ℝ)+1)/6)
    (C := densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s) ?_
  · convert hb using 1
    rw [show ((j : ℝ)+1)/6 - (j : ℝ)/6 = 1/6 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1/6)]
    ring
  · intro t ht
    have htr := piece_interval hj (Set.uIoc_subset_uIcc ht)
    rw [norm_mul]
    exact mul_le_mul (density_bound p j htr) (kernelMoment_bound' ell hs htr)
      (norm_nonneg _) (by have := densityBound_nonneg; positivity)


lemma K_bound (p : CardinalData) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K p ell s| ≤
      (25 * |p.C| + densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖)) * kernelEnvelope ell s := by
  have hatom : ‖(p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6))‖ ≤
      25 * |p.C| * kernelEnvelope ell s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |p.C| * (25 * kernelEnvelope ell s) := by
        gcongr; exact atomic_bound ell hs
      _ = _ := by ring
  have hsum : ‖∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.range 6,
        ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range 6,
        (densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6) := by
        exact Finset.sum_le_sum fun j hj => integral_piece_bound p ell j (Finset.mem_range.mp hj) hs
      _ = _ := by simp; ring
  unfold K
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by nlinarith))


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

lemma continuousOn_density (p : CardinalData) (j : ℕ) :
    ContinuousOn (density p j) (Set.Icc (0 : ℝ) 1) := by
  unfold density
  refine ((continuous_const.mul (continuous_u 0 j)).add
    (continuous_const.mul (continuous_v 0 j))).continuousOn.add ?_
  apply continuousOn_tsum (u := fun n : Node =>
    densityBound * (|p.x (n, false)| + |p.x (n, true)|))
  · intro n
    exact ((continuous_const.mul (continuous_u n.val j)).add
      (continuous_const.mul (continuous_v n.val j))).continuousOn
  · exact (X_summable_pairs p.x).mul_left densityBound
  · intro n t ht
    exact summand_bound p.x n j ht

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval hj ht) |>.intervalIntegrable

lemma density_positive_add (x y : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    density (positiveData (x+y)) j t = density (positiveData x) j t +
      density (positiveData y) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_add, Pi.add_apply, Complex.ofReal_add]
  simp_rw [add_mul]
  simp_rw [show ∀ n : Node,
    (x (n, false) : ℂ) * u n.val j t + (y (n, false) : ℂ) * u n.val j t +
    ((x (n, true) : ℂ) * v n.val j t + (y (n, true) : ℂ) * v n.val j t) =
    ((x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t) +
    ((y (n, false) : ℂ) * u n.val j t + (y (n, true) : ℂ) * v n.val j t) from fun n => by ring]
  exact (density_summable x j ht).tsum_add (density_summable y j ht)

lemma density_positive_smul (r : ℝ) (x : X) (j : ℕ) (t : ℝ) :
    density (positiveData (r • x)) j t = (r : ℂ) * density (positiveData x) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [mul_assoc, ← mul_add, tsum_mul_left]

lemma K_positive_add (x y : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (x+y)) ell s = K (positiveData x) ell s + K (positiveData y) ell s := by
  have hp (j : ℕ) (hj : j < 6) :
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData (x+y)) j t * kernelMoment ell s t) =
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData x) j t * kernelMoment ell s t) +
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData y) j t * kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_positive_add x y j (piece_interval hj ht), add_mul]
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  rw [← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)

lemma K_positive_smul (r : ℝ) (x : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (r • x)) ell s = r * K (positiveData x) ell s := by
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  change (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    density (positiveData (r • x)) j t * kernelMoment ell s t).re = _
  simp_rw [density_positive_smul, mul_assoc, intervalIntegral.integral_const_mul,
    ← Finset.mul_sum]
  simp [Complex.mul_re, positiveData]


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

noncomputable def nodeWeight (n : ℕ) : ℝ := (1 + |D n|) / Q n
noncomputable def allNodeWeight : ℝ := ∑ a ∈ residues, nodeWeight a

lemma nodeWeight_pos (n : ℕ) : 0 < nodeWeight n := by
  unfold nodeWeight
  exact div_pos (by positivity) (Q_pos n)

lemma allNodeWeight_nonneg : 0 ≤ allNodeWeight := by
  exact Finset.sum_nonneg fun a _ => (nodeWeight_pos a).le

lemma nodeWeight_le (n : Node) : nodeWeight n.val ≤ allNodeWeight := by
  have he : nodeWeight n.val = nodeWeight (n.val % 12) := by rw [nodeWeight, nodeWeight, Q_mod, D_mod]
  rw [he]
  exact Finset.single_le_sum (fun a _ => (nodeWeight_pos a).le) n.property.2

lemma K_positive_bound (x : X) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K (positiveData x) ell s| ≤ densityBound * ‖x‖ * kernelEnvelope ell s := by
  simpa [positiveData] using K_bound (positiveData x) ell hs

lemma Scoords_bound (x : X) (ni : Node × Bool) :
    |Scoords x ni| ≤ allNodeWeight * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  have he0 := kernelEnvelope_nonneg 0 (ni.1.val : ℝ)
  have he1 := kernelEnvelope_nonneg 1 (ni.1.val : ℝ)
  have hd := densityBound_nonneg
  have hx := norm_nonneg x
  have hq := Q_pos ni.1.val
  have hc0 := K_positive_bound x 0 (Nat.cast_nonneg ni.1.val)
  have hc1 := K_positive_bound x 1 (Nat.cast_nonneg ni.1.val)
  have hlocal : |Scoords x ni| ≤ nodeWeight ni.1.val * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
    unfold Scoords nodeWeight
    split
    · rw [abs_div, abs_of_pos hq]
      calc
        _ ≤ (|D ni.1.val| * |K (positiveData x) 0 ni.1.val| +
          |K (positiveData x) 1 ni.1.val|) / Q ni.1.val := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ (|D ni.1.val| * (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) +
          densityBound * ‖x‖ * kernelEnvelope 1 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) he1), mul_nonneg (mul_nonneg hd hx) he0]
    · rw [abs_div, abs_neg, abs_of_pos hq]
      calc
        _ ≤ (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) (add_nonneg he0 he1)),
            mul_nonneg (mul_nonneg hd hx) he1]
  exact hlocal.trans (by gcongr; exact nodeWeight_le ni.1)


lemma exp_nat_summable : Summable (fun n : ℕ => Real.exp (-kappa * n)) := by
  have he : Real.exp (-kappa) < 1 := by rw [Real.exp_lt_one_iff]; linarith [kappa_pos]
  have hh := summable_geometric_of_lt_one (Real.exp_pos (-kappa)).le he
  simpa only [← Real.exp_nat_mul, mul_comm] using hh

lemma kernelEnvelope_summable (ell : ℕ) : Summable (fun n : Node => kernelEnvelope ell n.val) := by
  have hh := exp_nat_summable.comp_injective (i := fun n : Node => n.val) Subtype.val_injective
  exact hh.mul_left ((1/(b*h)) * (Real.pi*(B/h+h))^ell)

lemma pairEnvelope_summable : Summable (fun ni : Node × Bool =>
    kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  apply (summable_prod_of_nonneg (fun ni =>
    add_nonneg (kernelEnvelope_nonneg _ _) (kernelEnvelope_nonneg _ _))).mpr
  constructor
  · intro n; exact Summable.of_finite
  · simpa only [tsum_bool] using
      ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1)).add
        ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1))

lemma Scoords_summable (x : X) : Summable (fun ni : Node × Bool => |Scoords x ni|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun ni => Scoords_bound x ni)
  exact pairEnvelope_summable.mul_left (allNodeWeight * densityBound * ‖x‖)

lemma Scoords_mem (x : X) : Memℓp (Scoords x) 1 := by
  apply memℓp_gen
  simpa using Scoords_summable x

lemma Scoords_add (x y : X) (ni : Node × Bool) :
    Scoords (x+y) ni = Scoords x ni + Scoords y ni := by
  unfold Scoords
  split <;> simp only [K_positive_add] <;> ring

lemma Scoords_smul (r : ℝ) (x : X) (ni : Node × Bool) :
    Scoords (r • x) ni = r * Scoords x ni := by
  unfold Scoords
  split <;> simp only [K_positive_smul] <;> ring

noncomputable def Slinear : X →ₗ[ℝ] X where
  toFun x := ⟨Scoords x, Scoords_mem x⟩
  map_add' x y := lp.ext (funext fun ni => Scoords_add x y ni)
  map_smul' r x := lp.ext (funext fun ni => Scoords_smul r x ni)

noncomputable def Sbound : ℝ := allNodeWeight * densityBound *
  ∑' ni : Node × Bool, (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val)

lemma Sbound_nonneg : 0 ≤ Sbound := by
  unfold Sbound
  exact mul_nonneg (mul_nonneg allNodeWeight_nonneg densityBound_nonneg)
    (tsum_nonneg (fun ni => add_nonneg (kernelEnvelope_nonneg _ _) (kernelEnvelope_nonneg _ _)))

lemma Slinear_bound (x : X) : ‖Slinear x‖ ≤ Sbound * ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs]
  change (∑' ni : Node × Bool, |Scoords x ni|) ≤ _
  calc
    _ ≤ ∑' ni : Node × Bool, allNodeWeight * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) :=
      (Scoords_summable x).tsum_le_tsum (fun ni => Scoords_bound x ni)
        (pairEnvelope_summable.mul_left _)
    _ = Sbound * ‖x‖ := by rw [tsum_mul_left]; unfold Sbound; ring


noncomputable def S : X →L[ℝ] X := Slinear.mkContinuous Sbound Slinear_bound

lemma S_apply (x : X) (ni : Node × Bool) : S x ni = Scoords x ni := rfl

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexLambda (t : ℂ) : ℂ :=
  Complex.I / ((b:ℂ) * (t+Complex.I*(h:ℂ)))
noncomputable def complexZ (t : ℂ) : ℂ :=
  -(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)

lemma complexLambda_real (t : ℝ) : complexLambda t = lambda t := rfl
lemma complexZ_real (t : ℝ) : complexZ t = z t := rfl


lemma reciprocal_disk_identity (a ζ : ℂ) (r : ℝ)
    (hΔ : Complex.normSq a-r^2 ≠ 0) :
    Complex.normSq (1-a*ζ)-r^2*Complex.normSq ζ =
      (Complex.normSq a-r^2)*Complex.normSq
        (ζ-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a) -
          r^2/(Complex.normSq a-r^2) := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,
    Complex.mul_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,zero_mul] at *
  simp only [← sq] at hΔ
  field_simp [hΔ]
  ring

lemma reciprocal_disk_bound {a u : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hΔ : 0 < Complex.normSq a-r^2) (hu : ‖u-a‖ ≤ r) (hu0 : u ≠ 0) :
    ‖u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a‖ ≤ r/(Complex.normSq a-r^2) := by
  let Δ := Complex.normSq a-r^2
  have hid := reciprocal_disk_identity a u⁻¹ r (ne_of_gt hΔ)
  have he : (1:ℂ)-a*u⁻¹ = (u-a)*u⁻¹ := by field_simp
  rw [he,Complex.normSq_mul,Complex.normSq_eq_norm_sq (u-a)] at hid
  have hnon : 0 ≤ Complex.normSq u⁻¹ := Complex.normSq_nonneg _
  have hsmall : Complex.normSq a-r^2 > 0 := hΔ
  have hprod : (‖u-a‖^2-r^2)*Complex.normSq u⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (u-a)]) hnon
  rw [Complex.normSq_eq_norm_sq (u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a)] at hid
  have hdpos : 0 < Δ := hΔ
  have hdne : Δ ≠ 0 := ne_of_gt hdpos
  have hratio : 0 ≤ r/Δ := div_nonneg hr hdpos.le
  have hn := norm_nonneg (u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)
  have hsq : ‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ (r/Δ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hdpos)).mp
    have heq : Δ^2*(r/Δ)^2 = r^2 := by field_simp
    rw [heq]
    have hprod' : Δ*‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ r^2/Δ := by
      dsimp [Δ]
      nlinarith only [hid,hprod]
    have hh := mul_le_mul_of_nonneg_left hprod' hdpos.le
    have heq' : Δ*(r^2/Δ) = r^2 := by field_simp
    rw [heq'] at hh
    nlinarith only [hh]
  dsimp [Δ] at *
  nlinarith only [hsq, hn, hratio]


noncomputable def diskCenter (j : ℕ) : ℝ := (2*(j:ℝ)+1)/12

lemma disk_coordinate_bounds {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖t‖ ≤ 13/12 ∧ -(1/6:ℝ) ≤ t.im ∧ t.im ≤ 1/6 := by
  have hc0 : 0 ≤ diskCenter j := by unfold diskCenter; positivity
  have hc1 : diskCenter j ≤ 11/12 := by
    unfold diskCenter
    have : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
    linarith
  have hi := (Complex.abs_im_le_norm (t-(diskCenter j:ℂ))).trans ht
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,abs_le] at hi
  refine ⟨?_, hi⟩
  have hn := norm_add_le (t-(diskCenter j:ℂ)) (diskCenter j:ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0] at hn
  linarith

lemma disk_denominator_lower {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    7/30 ≤ ‖t+Complex.I*(h:ℂ)‖ := by
  have hi := (disk_coordinate_bounds hj ht).2.1
  have hn := (le_abs_self (t+Complex.I*(h:ℂ)).im).trans (Complex.abs_im_le_norm _)
  simp only [Complex.add_im,Complex.I_mul_im,Complex.ofReal_re] at hn
  norm_num [h] at hn ⊢
  linarith

lemma disk_denominator_ne {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : t+Complex.I*(h:ℂ) ≠ 0 := by
  have hb := disk_denominator_lower hj ht
  intro he
  rw [he,norm_zero] at hb
  norm_num at hb

lemma b_lower_simple : 43/50 < b := by
  have hh := b_sq
  have hp := b_pos
  nlinarith

lemma disk_lambda_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexLambda t‖ < 5 := by
  have hd := disk_denominator_lower hj ht
  have hb := b_lower_simple
  rw [complexLambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos b_pos]
  apply (div_lt_iff₀ (mul_pos b_pos (by linarith))).mpr
  nlinarith

lemma disk_z_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexZ t‖ < 31/5 := by
  have hd := disk_denominator_lower hj ht
  have hm := norm_sub_le (-(B:ℂ)/(t+Complex.I*(h:ℂ))) (Complex.I*(h:ℂ))
  simp only [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,norm_mul,
    Complex.norm_I,one_mul,abs_of_pos B_pos,abs_of_pos h_pos] at hm
  have hb : B/‖t+Complex.I*(h:ℂ)‖ ≤ (40:ℝ)/7 := by
    apply (div_le_iff₀ (by linarith : 0 < ‖t+Complex.I*(h:ℂ)‖)).mpr
    norm_num [B]
    linarith
  change ‖-(B:ℂ)/(t+Complex.I*(h:ℂ))-Complex.I*(h:ℂ)‖ < _
  norm_num [h] at hm hb ⊢
  linarith

lemma disk_delta_bounds {j : ℕ} (hj : j < 6) :
    167/1200 ≤ Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ∧
    Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ≤ 389/400 := by
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hj5 : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_mul_re,Complex.I_mul_im,
    neg_zero,add_zero,zero_add]
  unfold diskCenter h
  constructor <;> nlinarith [sq_nonneg (j:ℝ)]

lemma disk_z_imaginary {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(1402/17505:ℝ) ≤ (complexZ t).im := by
  let a : ℂ := (diskCenter j:ℂ)+Complex.I*(h:ℂ)
  let Δ : ℝ := Complex.normSq a-(1/6:ℝ)^2
  have hΔ : 0 < Δ := by
    have hh := (disk_delta_bounds hj).1
    change 167/1200 ≤ Δ at hh
    linarith
  have hΔ1 : Δ ≤ 389/400 := (disk_delta_bounds hj).2
  have hrec := reciprocal_disk_bound (a:=a) (u:=t+Complex.I*(h:ℂ))
    (by norm_num : (0:ℝ) ≤ 1/6) hΔ
    (by simpa [a] using ht) (disk_denominator_ne hj ht)
  have hi := (le_abs_self _).trans ((Complex.abs_im_le_norm
    ((t+Complex.I*(h:ℂ))⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)).trans hrec)
  have haim : a.im = h := by simp [a]
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_im,zero_mul,add_zero,haim] at hi
  change (t+Complex.I*(h:ℂ))⁻¹.im-Δ⁻¹*(-h) ≤ (1/6)/Δ at hi
  have htop : (t+Complex.I*(h:ℂ))⁻¹.im ≤ ((1/6:ℝ)-h)/Δ := by
    rw [div_eq_mul_inv] at hi ⊢
    nlinarith only [hi]
  have heq : (complexZ t).im = -B*(t+Complex.I*(h:ℂ))⁻¹.im-h := by
    simp [complexZ,div_eq_mul_inv,Complex.mul_im]
  rw [heq]
  have hb := mul_le_mul_of_nonpos_left htop (neg_nonpos.mpr B_pos.le)
  have hq : -(1402/17505:ℝ) ≤ -B*((1/6-h)/Δ)-h := by
    have hh : (-(1402/17505:ℝ)+h)*Δ ≤ -B*(1/6-h) := by
      norm_num [B,h] at *
      nlinarith
    have hh' := (le_div_iff₀ hΔ).mpr hh
    linear_combination hh'
  linarith

lemma disk_z_imaginary_simple {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    -(81/1000:ℝ) < (complexZ t).im := by
  have hh := disk_z_imaginary hj ht
  linarith

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set


noncomputable def complexU (n j : ℕ) (t : ℂ) : ℂ :=
  -2 * (Real.pi:ℂ)^2 * Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)
noncomputable def complexV (n j : ℕ) (t : ℂ) : ℂ :=
  2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

lemma complexU_real (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_real (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl

lemma disk_frequency_distance {j : ℕ} (hj : j < 6) {l : ℕ}
    (hl : l ∈ Finset.Icc (j+1) 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖(l:ℂ)/6-t‖ ≤ 13/12 := by
  have hjr : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hl1 : (l:ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hh : ‖(l:ℂ)/6-(diskCenter j:ℂ)‖ ≤ 11/12 := by
    rw [show (l:ℂ)/6-(diskCenter j:ℂ) = (((l:ℝ)/6-diskCenter j:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    unfold diskCenter
    constructor <;> linarith
  have hn := norm_sub_le ((l:ℂ)/6-(diskCenter j:ℂ)) (t-(diskCenter j:ℂ))
  rw [sub_sub_sub_cancel_right] at hn
  linarith

lemma disk_phase_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ ≤ Real.exp (100*Real.pi/6) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have ht' := (disk_coordinate_bounds hj ht).2.2
  have hn' : (n:ℝ) ≤ 100 := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,
    mul_zero,sub_zero,neg_zero,Complex.mul_im,zero_add]
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hn0,
    mul_nonneg Real.pi_pos.le (show 0 ≤ 100-(n:ℝ) by linarith)]

lemma complexU_disk_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexU n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ (13/12)*10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, (13/12)*‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul,norm_mul,atom_phase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right (disk_frequency_distance hj hl ht) (norm_nonneg _)
      _ ≤ (13/12)*10 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (positive_coeff_mass_le j) (by norm_num)
  unfold complexU
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi^2 * Real.exp (100*Real.pi/6) * ((13/12)*10) := by
      gcongr
      exact disk_phase_bound hj hn ht
    _ ≤ _ := by
      have hp := Real.pi_lt_d2
      have hp0 := Real.pi_pos
      have hp2 : Real.pi^2 < 10 := by nlinarith
      have he := Real.exp_pos (100*Real.pi/6)
      nlinarith

lemma complexV_disk_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexV n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul,atom_phase_norm,mul_one]
      _ ≤ 10 := positive_coeff_mass_le j
  unfold complexV
  simp only [norm_mul,Complex.norm_I,Complex.norm_ofNat,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi*Real.exp (100*Real.pi/6)*10 := by
      gcongr
      exact disk_phase_bound hj hn ht
    _ ≤ _ := by
      have := Real.pi_lt_d2
      have := Real.exp_pos (100*Real.pi/6)
      nlinarith

noncomputable def finiteDensity (c d : ℕ → ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 101, ((c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t)

lemma finiteDensity_disk_bound (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖finiteDensity c d j t‖ ≤ 1000*Real.exp (100*Real.pi/6) := by
  unfold finiteDensity
  calc
    _ ≤ ∑ n ∈ Finset.range 101, ‖(c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range 101, (|c n|+|d n|)*(250*Real.exp (100*Real.pi/6)) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ‖(c n:ℂ)*complexU n j t‖ + ‖(d n:ℂ)*complexV n j t‖ := norm_add_le _ _
        _ ≤ |c n| *(250*Real.exp (100*Real.pi/6)) + |d n| *(250*Real.exp (100*Real.pi/6)) := by
          simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          gcongr
          · exact complexU_disk_bound hj (by have := Finset.mem_range.mp hn; omega) ht
          · exact complexV_disk_bound hj (by have := Finset.mem_range.mp hn; omega) ht
        _ = _ := by ring
    _ ≤ 3*(250*Real.exp (100*Real.pi/6)) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ _ := by have := Real.exp_pos (100*Real.pi/6); linarith

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexDirectFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (Complex.I*Real.pi*t*m) * (Complex.I*Real.pi*t*y)^ell / (ell.factorial:ℂ)
noncomputable def complexTransformedFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  complexLambda t * Complex.exp (Complex.I*Real.pi*complexZ t*m) *
    (Complex.I*Real.pi*complexZ t*y)^ell / (ell.factorial:ℂ)

lemma divided_power_norm (w : ℂ) (ell : ℕ) :
    ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖ := by
  simpa only [norm_div,norm_pow,Complex.norm_natCast] using
    Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) ell

lemma phase_exp_norm_bound {w : ℂ} {m L : ℝ} (hm : 0 ≤ m) (hw : -L ≤ w.im) :
    ‖Complex.exp (Complex.I*Real.pi*w*m)‖ ≤ Real.exp (Real.pi*m*L) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,
    zero_sub,sub_zero,zero_add]
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hm) (show 0 ≤ w.im+L by linarith)]

lemma complexDirectFactor_disk_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) {m y : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖complexDirectFactor m y ell t‖ ≤ Real.exp (Real.pi*(100/6+13/8)) := by
  have htn := (disk_coordinate_bounds hj ht).1
  have hti := (disk_coordinate_bounds hj ht).2.1
  have he : ‖Complex.exp (Complex.I*Real.pi*t*m)‖ ≤ Real.exp (Real.pi*100/6) := by
    refine (phase_exp_norm_bound hm0 hti).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp : ‖(Complex.I*Real.pi*t*y)^ell/(ell.factorial:ℂ)‖ ≤
      Real.exp (Real.pi*(13/8)) := by
    refine (divided_power_norm _ ell).trans (Real.exp_le_exp.mpr ?_)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hh := mul_le_mul htn hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 13/12)
    nlinarith [Real.pi_pos]
  rw [complexDirectFactor,mul_div_assoc,norm_mul]
  calc
    _ ≤ Real.exp (Real.pi*100/6)*Real.exp (Real.pi*(13/8)) :=
      mul_le_mul he hp (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma complexTransformedFactor_disk_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) {m y : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖complexTransformedFactor m y ell t‖ ≤ 5*Real.exp (Real.pi*(87/5)) := by
  have htn := (disk_z_bound hj ht).le
  have hti := (disk_z_imaginary_simple hj ht).le
  have he : ‖Complex.exp (Complex.I*Real.pi*complexZ t*m)‖ ≤ Real.exp (Real.pi*(81/10)) := by
    refine (phase_exp_norm_bound hm0 hti).trans ?_
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hp : ‖(Complex.I*Real.pi*complexZ t*y)^ell/(ell.factorial:ℂ)‖ ≤
      Real.exp (Real.pi*(93/10)) := by
    refine (divided_power_norm _ ell).trans (Real.exp_le_exp.mpr ?_)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hh := mul_le_mul htn hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 31/5)
    nlinarith [Real.pi_pos]
  rw [complexTransformedFactor,mul_div_assoc,norm_mul,norm_mul]
  calc
    _ ≤ (5*Real.exp (Real.pi*(81/10)))*Real.exp (Real.pi*(93/10)) :=
      mul_le_mul (mul_le_mul (disk_lambda_bound hj ht).le he (norm_nonneg _)
        (by norm_num)) hp (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

lemma numerical_moment_bound : (5000:ℝ)*Real.exp 111 < (10:ℝ)^53 := by
  have he : Real.exp 1 < 11/4 := by linarith [Real.exp_one_lt_d9]
  have hex : Real.exp 111 = (Real.exp 1)^111 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hex]
  have hp : (Real.exp 1)^111 ≤ (11/4:ℝ)^111 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 111
  calc
    _ ≤ 5000*(11/4:ℝ)^111 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ < _ := by norm_num

lemma directIntegrand_disk_bound (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexDirectFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  rw [norm_mul]
  calc
    _ ≤ (1000*Real.exp (100*Real.pi/6))*Real.exp (Real.pi*(100/6+13/8)) :=
      mul_le_mul (finiteDensity_disk_bound c d hw hj ht)
        (complexDirectFactor_disk_bound hj ht hm0 hm1 hy ell) (norm_nonneg _) (by positivity)
    _ ≤ 5000*Real.exp 111 := by
      rw [mul_assoc,← Real.exp_add]
      apply mul_le_mul (by norm_num) _ (Real.exp_pos _).le (by norm_num)
      apply Real.exp_le_exp.mpr
      have hp := Real.pi_lt_d4
      linarith
    _ ≤ _ := numerical_moment_bound.le

lemma transformedIntegrand_disk_bound (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6)
    {m y : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (hy : |y| ≤ 3/2) (ell : ℕ) :
    ‖finiteDensity c d j t * complexTransformedFactor m y ell t‖ ≤ (10:ℝ)^53 := by
  rw [norm_mul]
  calc
    _ ≤ (1000*Real.exp (100*Real.pi/6))*(5*Real.exp (Real.pi*(87/5))) :=
      mul_le_mul (finiteDensity_disk_bound c d hw hj ht)
        (complexTransformedFactor_disk_bound hj ht hm0 hm1 hy ell) (norm_nonneg _) (by positivity)
    _ = 5000*Real.exp ((100*Real.pi/6)+Real.pi*(87/5)) := by rw [Real.exp_add]; ring
    _ ≤ 5000*Real.exp 111 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hp := Real.pi_lt_d4
      linarith
    _ ≤ _ := numerical_moment_bound.le

end SharpPlanar

end OAI
