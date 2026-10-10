import Mathlib

namespace OAI

/-! Harmonic sine estimates, Fourier windows, tracial Hilbert spaces and unitary power rigidity. -/

noncomputable section


namespace HochschildRigidity
open Finset

 
theorem norm_sum_smul_le_of_antitone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ) (z : ℕ → E) (B : ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfmono : Antitone f) (hB : 0 ≤ B)
    (hz : ∀ k, ‖∑ i ∈ range k, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ range n, f i • z i‖ ≤ f 0 * B := by
  cases n with
  | zero => simpa using mul_nonneg (hf 0) hB
  | succ n =>
    rw [sum_range_by_parts, Nat.succ_sub_one]
    have hd (i : ℕ) : 0 ≤ f i - f (i + 1) := sub_nonneg.mpr (hfmono (Nat.le_succ i))
    have heq : -(∑ i ∈ range n, (f (i + 1) - f i) • ∑ j ∈ range (i + 1), z j) =
        ∑ i ∈ range n, (f i - f (i + 1)) • ∑ j ∈ range (i + 1), z j := by
      simp only [← Finset.sum_neg_distrib, ← neg_smul, neg_sub]
    rw [sub_eq_add_neg, heq]
    calc
      _ ≤ ‖f n • ∑ i ∈ range (n + 1), z i‖ +
          ‖∑ i ∈ range n, (f i - f (i + 1)) • ∑ j ∈ range (i + 1), z j‖ := norm_add_le _ _
      _ ≤ f n * B + ∑ i ∈ range n, (f i - f (i + 1)) * B := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf n)]
          exact mul_le_mul_of_nonneg_left (hz _) (hf n)
        · refine (norm_sum_le _ _).trans (sum_le_sum (fun i _ => ?_))
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i)]
          exact mul_le_mul_of_nonneg_left (hz _) (hd i)
      _ = f 0 * B := by
        rw [← sum_mul, sum_range_sub']
        ring

 
theorem abs_sum_sin_le (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (b : ℝ) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (t * i + b)| ≤ Real.pi / t := by
  have hspos : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod : Real.sin (t / 2) * |∑ i ∈ range n, Real.sin (t * i + b)| ≤ 1 := by
    have heq := congrArg abs (Real.sin_mul_sum_sin n t b)
    rw [abs_mul, abs_of_pos hspos, abs_mul] at heq
    rw [heq]
    calc
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ 1 := by simpa using Real.abs_sin_le_one _
  have hsin : t / Real.pi ≤ Real.sin (t / 2) := by
    simpa using Real.mul_le_sin (x := t / 2) (by positivity) (by linarith)
  calc
    _ ≤ 1 / Real.sin (t / 2) := (le_div_iff₀ hspos).mpr (by nlinarith [hprod])
    _ ≤ Real.pi / t := (div_le_div_iff₀ hspos ht).mpr (by
      have h := (div_le_iff₀ Real.pi_pos).mp hsin
      nlinarith)

 
theorem abs_harmonic_sin_tail_le (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (p : ℕ) (hp : 0 < p) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((p + i : ℕ) : ℝ) * t) / (p + i)| ≤
      Real.pi / (t * p) := by
  let f : ℕ → ℝ := fun i => 1 / (p + i : ℕ)
  let z : ℕ → ℝ := fun i => Real.sin (((p + i : ℕ) : ℝ) * t)
  have hf (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  have hfm : Antitone f := by
    intro i j hij
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_left hij p
  have hz (k : ℕ) : ‖∑ i ∈ range k, z i‖ ≤ Real.pi / t := by
    simpa [z, Real.norm_eq_abs, Nat.cast_add, add_mul, mul_add, mul_comm, add_comm] using
      abs_sum_sin_le t ht htpi (p * t) k
  have h := norm_sum_smul_le_of_antitone f z (Real.pi / t) hf hfm
    (by positivity) hz n
  simpa [f, z, Real.norm_eq_abs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem abs_harmonic_sin_prefix_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ n * t := by
  calc
    _ ≤ ∑ i ∈ range n, |Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, t := by
      apply sum_le_sum
      intro i _
      have hi : (0 : ℝ) < i + 1 := by positivity
      rw [abs_div, abs_of_pos hi]
      apply (div_le_iff₀ hi).mpr
      have h := Real.abs_sin_le_abs (x := ((i + 1 : ℕ) : ℝ) * t)
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht)] at h
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
    _ = n * t := by simp

 
theorem abs_harmonic_sin_le_pos (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ 1 + Real.pi := by
  let K : ℕ := ⌊1 / t⌋₊
  have hK : (K : ℝ) * t ≤ 1 := by
    have h := Nat.floor_le (show 0 ≤ 1 / t by positivity)
    exact (le_div_iff₀ ht).mp h
  by_cases hn : n ≤ K
  · calc
      _ ≤ (n : ℝ) * t := abs_harmonic_sin_prefix_le t ht.le n
      _ ≤ (K : ℝ) * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le
      _ ≤ 1 := hK
      _ ≤ 1 + Real.pi := by linarith [Real.pi_pos]
  · have hKn : K ≤ n := by omega
    have hp : (0 : ℝ) < t * (K + 1) := by positivity
    have htK : 1 ≤ t * (K + 1) := by
      have h : 1 / t < (K : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
      have h' := (div_lt_iff₀ ht).mp h
      nlinarith
    have htail := abs_harmonic_sin_tail_le t ht htpi (K + 1) (by omega) (n - K)
    have htail' :
        |∑ i ∈ range (n - K), Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)|
          ≤ Real.pi := by
      calc
        _ ≤ Real.pi / (t * (K + 1)) := by
          simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            add_assoc, add_comm, add_left_comm] using htail
        _ ≤ Real.pi := (div_le_iff₀ hp).mpr (by nlinarith [Real.pi_pos])
    rw [show n = K + (n - K) by omega, sum_range_add]
    calc
      _ ≤ |∑ i ∈ range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| +
          |∑ i ∈ range (n - K), Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)| :=
        by
          simpa only [Nat.cast_add] using
            (abs_add_le
              (∑ i ∈ range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1))
              (∑ i ∈ range (n - K),
                Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)))
      _ ≤ (K : ℝ) * t + Real.pi := add_le_add
        (abs_harmonic_sin_prefix_le t ht.le K) htail'
      _ ≤ 1 + Real.pi := by linarith

 
theorem abs_harmonic_sin_le (t : ℝ) (ht : |t| ≤ Real.pi) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ 1 + Real.pi := by
  rcases lt_trichotomy 0 t with hpos | rfl | hneg
  · exact abs_harmonic_sin_le_pos t hpos ((le_abs_self _).trans ht) n
  · simp only [mul_zero, Real.sin_zero, zero_div, sum_const_zero, abs_zero]
    positivity
  · have h := abs_harmonic_sin_le_pos (-t) (by linarith) (by
        simpa only [abs_of_neg hneg] using ht) n
    simpa only [mul_neg, Real.sin_neg, neg_div, sum_neg_distrib, abs_neg] using h

 
noncomputable def harmonicPolynomial {A : Type*} [Ring A] [Algebra ℂ A]
    (n : ℕ) (x : A) : A :=
  ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)

 
theorem harmonicPolynomial_im (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    (harmonicPolynomial n z).im =
      ∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * z.arg) / (i + 1) := by
  have hpower (k : ℕ) : (z ^ k).im = Real.sin ((k : ℝ) * z.arg) := by
    have hzrep := Complex.norm_mul_cos_add_sin_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at hzrep
    have h := congrArg Complex.im (Complex.cos_add_sin_mul_I_pow k (z.arg : ℂ))
    rw [hzrep] at h
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using h
  simp only [harmonicPolynomial, Complex.im_sum, smul_eq_mul]
  apply sum_congr rfl
  intro i _
  rw [show (i + 1 : ℂ)⁻¹ = (((i + 1 : ℝ)⁻¹ : ℝ) : ℂ) by simp]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hpower]
  ring

theorem norm_harmonicPolynomial_sub_star_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖harmonicPolynomial n z - star (harmonicPolynomial n z)‖ ≤
      2 * (1 + Real.pi) := by
  have h := abs_harmonic_sin_le z.arg (Complex.abs_arg_le_pi z) n
  rw [← harmonicPolynomial_im z hz n] at h
  change ‖harmonicPolynomial n z - (starRingEnd ℂ) (harmonicPolynomial n z)‖ ≤ _
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

 
theorem norm_unitary_harmonicPolynomial_sub_star_le {A : Type*} [CStarAlgebra A]
    (u : unitary A) (n : ℕ) :
    ‖harmonicPolynomial n (u : A) - star (harmonicPolynomial n (u : A))‖ ≤
      2 * (1 + Real.pi) := by
  have hcfc : cfc (harmonicPolynomial n : ℂ → ℂ) (u : A) =
      harmonicPolynomial n (u : A) := by
    unfold harmonicPolynomial
    rw [show (fun x : ℂ => ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)) =
        ∑ i ∈ range n, (fun x : ℂ => ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)) by
      ext; simp only [Finset.sum_apply]]
    rw [cfc_sum (fun (i : ℕ) (x : ℂ) => ((i + 1 : ℂ)⁻¹) • x ^ (i + 1))
      (u : A) (range n) (by intro i _; fun_prop)]
    apply sum_congr rfl
    intro i _
    rw [cfc_smul ((i + 1 : ℂ)⁻¹) (fun x : ℂ => x ^ (i + 1)) (u : A) (by fun_prop),
      cfc_pow_id (R := ℂ) (u : A) (i + 1)]
  have hcont : Continuous (harmonicPolynomial n : ℂ → ℂ) := by
    unfold harmonicPolynomial
    fun_prop
  have h := norm_cfc_le (a := (u : A)) (f := fun z : ℂ =>
      harmonicPolynomial n z - star (harmonicPolynomial n z))
    (show 0 ≤ 2 * (1 + Real.pi) by positivity)
    (fun z hz => norm_harmonicPolynomial_sub_star_le z
      (spectrum.norm_eq_one_of_unitary u.property hz) n)
  rwa [cfc_sub _ _ _ hcont.continuousOn hcont.star.continuousOn, cfc_star, hcfc] at h

section FourierWindows
variable {L : ℕ} [NeZero L]

lemma sum_stdAddChar_mul (t : ZMod L) :
    ∑ j : ZMod L, ZMod.stdAddChar (t * j) = if t = 0 then (L : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L ht)

 
theorem sum_dft_mul_star_dft {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (f g : ZMod L → A) :
    ∑ j : ZMod L, ZMod.dft f j * star (ZMod.dft g j) =
      (L : ℂ) • ∑ k : ZMod L, f k * star (g k) := by
  simp only [ZMod.dft_apply, star_sum, star_smul, sum_mul, mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_sum, smul_smul]
  simp only [Complex.star_def, ← AddChar.map_neg_eq_conj, neg_neg,
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  rw [sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [sum_comm]
  simp only [← sum_smul, sum_stdAddChar_mul, sub_eq_zero, ite_smul, zero_smul,
    sum_ite_eq, mem_univ, ite_true, ← smul_sum]

noncomputable def rootUnitary (j : ZMod L) : unitary ℂ :=
  ⟨ZMod.stdAddChar j, by
    rw [Unitary.mem_iff]
    simp only [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      neg_add_cancel, add_neg_cancel, AddChar.map_zero_eq_one, and_self]⟩

@[simp] lemma rootUnitary_coe (j : ZMod L) :
    (rootUnitary j : ℂ) = ZMod.stdAddChar j := rfl

noncomputable def fourierWindow {A : Type*} [Ring A] [Algebra ℂ A]
    (u : A) (j : ZMod L) : A :=
  (L : ℂ)⁻¹ • ZMod.dft (fun k : ZMod L => u ^ k.val) j

lemma sum_fourierWindow_mul_star {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (u : unitary A) :
    ∑ j : ZMod L, fourierWindow (u : A) j * star (fourierWindow (u : A) j) = 1 := by
  have hpow (k : ZMod L) : (u : A) ^ k.val * star ((u : A) ^ k.val) = 1 := by
    simpa only [Unitary.coe_star, SubmonoidClass.coe_pow] using Unitary.coe_mul_star_self (u ^ k.val)
  simp only [fourierWindow, star_smul, smul_mul_smul_comm, star_inv₀, star_natCast,
    ← smul_sum, sum_dft_mul_star_dft, hpow, sum_const, card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  rw [show (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * (L : ℂ) * (L : ℂ) = 1 by field_simp]
  exact one_smul _ _

lemma sum_zmod_val {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ k : ZMod L, f k.val = ∑ k ∈ range L, f k := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ L => exact Fin.sum_univ_eq_sum_range f (L + 1)

lemma fourierWindow_eq_geometric {A : Type*} [Ring A] [Algebra ℂ A]
    (u : A) (j : ZMod L) :
    fourierWindow u j = (L : ℂ)⁻¹ •
      ∑ k ∈ range L, (ZMod.stdAddChar (-j) • u) ^ k := by
  unfold fourierWindow
  rw [ZMod.dft_apply]
  congr 1
  calc
    _ = ∑ k : ZMod L, (ZMod.stdAddChar (-j) • u) ^ k.val := by
      apply sum_congr rfl
      intro k _
      rw [smul_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
        ZMod.natCast_zmod_val, mul_neg]
    _ = _ := sum_zmod_val _

 
lemma norm_unitary_mul_fourierWindow_sub_le {A : Type*} [CStarAlgebra A]
    [Nontrivial A] (u : unitary A) (j : ZMod L) :
    ‖((rootUnitary (-j) • u : unitary A) : A) * fourierWindow (u : A) j -
      fourierWindow (u : A) j‖ ≤ 2 / (L : ℝ) := by
  let v : unitary A := rootUnitary (-j) • u
  have hq : fourierWindow (u : A) j =
      (L : ℂ)⁻¹ • ∑ k ∈ range L, (v : A) ^ k := fourierWindow_eq_geometric _ _
  have heq : (v : A) * fourierWindow (u : A) j - fourierWindow (u : A) j =
      (L : ℂ)⁻¹ • ((v : A) ^ L - 1) := by
    rw [← sub_one_mul, hq, mul_smul_comm, mul_geom_sum]
  change ‖(v : A) * fourierWindow (u : A) j - fourierWindow (u : A) j‖ ≤ _
  rw [heq, norm_smul, norm_inv, Complex.norm_natCast]
  have hpow : ‖(v : A) ^ L‖ = 1 := by
    simpa only [SubmonoidClass.coe_pow] using CStarRing.norm_coe_unitary (v ^ L)
  calc
    _ ≤ (L : ℝ)⁻¹ * (‖(v : A) ^ L‖ + ‖(1 : A)‖) := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [hpow, norm_one]; ring

lemma norm_unitary_pow_mul_sub_le {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) (k : ℕ) :
    ‖(v : A) ^ k * q - q‖ ≤ (k : ℝ) * ‖(v : A) * q - q‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : (v : A) ^ (k + 1) * q - q =
          (v : A) * ((v : A) ^ k * q - q) + ((v : A) * q - q) := by
        rw [pow_succ', mul_sub, ← mul_assoc]; noncomm_ring
      rw [heq]
      calc
        _ ≤ ‖(v : A) * ((v : A) ^ k * q - q)‖ + ‖(v : A) * q - q‖ := norm_add_le _ _
        _ = ‖(v : A) ^ k * q - q‖ + ‖(v : A) * q - q‖ := by
          rw [CStarRing.norm_coe_unitary_mul]
        _ ≤ (k : ℝ) * ‖(v : A) * q - q‖ + ‖(v : A) * q - q‖ := by gcongr
        _ = _ := by push_cast; ring

lemma norm_star_unitary_mul_sub {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) :
    ‖(star v : A) * q - q‖ = ‖(v : A) * q - q‖ := by
  rw [← CStarRing.norm_coe_unitary_mul v ((star v : A) * q - q), mul_sub,
    ← mul_assoc, Unitary.mul_star_self_of_mem v.property, one_mul, norm_sub_rev]

lemma norm_harmonicPolynomial_mul_sub_le {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) (n : ℕ) :
    ‖harmonicPolynomial n (v : A) * q - (harmonic n : ℂ) • q‖ ≤
      (n : ℝ) * ‖(v : A) * q - q‖ := by
  have heq : harmonicPolynomial n (v : A) * q - (harmonic n : ℂ) • q =
      ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • ((v : A) ^ (i + 1) * q - q) := by
    simp [harmonicPolynomial, harmonic, smul_sub, sum_mul,
      sum_smul, sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ range n, ‖((i + 1 : ℂ)⁻¹) • ((v : A) ^ (i + 1) * q - q)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range n, ‖(v : A) * q - q‖ := by
      apply sum_le_sum
      intro i _
      rw [norm_smul, norm_inv, ← Nat.cast_one (R := ℂ), ← Nat.cast_add,
        Complex.norm_natCast]
      calc
        _ ≤ ((i + 1 : ℕ) : ℝ)⁻¹ *
            (((i + 1 : ℕ) : ℝ) * ‖(v : A) * q - q‖) := by
          gcongr
          exact norm_unitary_pow_mul_sub_le v q (i + 1)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = _ := by simp

lemma star_harmonicPolynomial {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (v : A) (n : ℕ) :
    star (harmonicPolynomial n v) = harmonicPolynomial n (star v) := by
  simp [harmonicPolynomial, star_sum, star_smul, star_pow]

lemma power_multiplier_smul {A : Type*} [CStarAlgebra A] (S : A →L[ℂ] A)
    (u a : A) (hS : ∀ k : ℕ, 0 < k → S (u ^ k) = a * u ^ k) (c : ℂ) :
    ∀ k : ℕ, 0 < k → S ((c • u) ^ k) = a * (c • u) ^ k := by
  intro k hk
  rw [smul_pow, map_smul, hS k hk, mul_smul_comm]

lemma map_harmonicPolynomial {A : Type*} [CStarAlgebra A] (S : A →L[ℂ] A)
    (u a : A) (hS : ∀ k : ℕ, 0 < k → S (u ^ k) = a * u ^ k) (n : ℕ) :
    S (harmonicPolynomial n u) = a * harmonicPolynomial n u := by
  simp only [harmonicPolynomial, map_sum, map_smul, hS _ (Nat.succ_pos _),
    mul_sum, mul_smul_comm]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
lemma preGNS_norm_mul_le (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖a‖ * ‖τ.toPreGNS b‖ := by
  calc
    _ = ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖ := rfl
    _ ≤ ‖τ.leftMulMapPreGNS a‖ * ‖τ.toPreGNS b‖ :=
      (τ.leftMulMapPreGNS a).le_opNorm _
    _ ≤ _ := by
      gcongr
      unfold PositiveLinearMap.leftMulMapPreGNS
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
lemma preGNS_norm_one (h1 : τ 1 = 1) : ‖τ.toPreGNS 1‖ = 1 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS 1))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
  nlinarith [norm_nonneg (τ.toPreGNS 1)]
lemma preGNS_norm_le (h1 : τ 1 = 1) (a : A) : ‖τ.toPreGNS a‖ ≤ ‖a‖ := by
  simpa only [mul_one, preGNS_norm_one τ h1] using preGNS_norm_mul_le τ a 1
lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _
lemma preGNS_norm_mul_right_le (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖τ.toPreGNS a‖ := by
  rw [← preGNS_norm_star τ htr, star_mul]
  exact (preGNS_norm_mul_le τ (star b) (star a)).trans_eq
    (by rw [norm_star, preGNS_norm_star τ htr])
lemma preGNS_norm_eq_zero_iff
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    ‖τ.toPreGNS a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hf
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, h, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0)] using (τ.preGNS_norm_sq (τ.toPreGNS a)).symm
  · rintro rfl
    simp

open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
lemma sum_preGNS_norm_mul_sq (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (q : ι → A) (hq : ∑ j, q j * star (q j) = 1) (a : A) :
    ∑ j, ‖τ.toPreGNS (a * q j)‖ ^ 2 = ‖τ.toPreGNS a‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    _ = ∑ j, τ ((star a * a) * (q j * star (q j))) := by
      apply sum_congr rfl
      intro j _
      simpa only [mul_assoc] using htr (star (q j)) ((star a * a) * q j)
    _ = τ ((star a * a) * ∑ j, q j * star (q j)) := by rw [mul_sum, map_sum]
    _ = _ := by rw [hq, mul_one]

noncomputable def gnsFamily (f : ι → A) : PiLp 2 (fun _ : ι => τ.PreGNS) :=
  WithLp.toLp 2 (fun j => τ.toPreGNS (f j))

lemma norm_gnsFamily_sq (f : ι → A) :
    ‖gnsFamily τ f‖ ^ 2 = ∑ j, ‖τ.toPreGNS (f j)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_add (f g : ι → A) :
    gnsFamily τ (fun j => f j + g j) = gnsFamily τ f + gnsFamily τ g := by
  ext j
  exact map_add τ.toPreGNS _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_sub (f g : ι → A) :
    gnsFamily τ (fun j => f j - g j) = gnsFamily τ f - gnsFamily τ g := by
  ext j
  exact map_sub τ.toPreGNS _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_smul (c : ℂ) (f : ι → A) :
    gnsFamily τ (fun j => c • f j) = c • gnsFamily τ f := by
  ext j
  exact map_smul τ.toPreGNS _ _

lemma norm_gnsFamily_mul (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (q : ι → A) (hq : ∑ j, q j * star (q j) = 1) (a : A) :
    ‖gnsFamily τ (fun j => a * q j)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_gnsFamily_sq, sum_preGNS_norm_mul_sq τ htr q hq]

lemma norm_gnsFamily_leftMul_le (a f : ι → A) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) :
    ‖gnsFamily τ (fun j => a j * f j)‖ ≤ C * ‖gnsFamily τ f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, norm_gnsFamily_sq, norm_gnsFamily_sq, mul_sum]
  apply sum_le_sum
  intro j _
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (preGNS_norm_mul_le τ _ _).trans (by gcongr; exact ha j)

lemma norm_gnsFamily_sq_le (h1 : τ 1 = 1) (f : ι → A) (C : ℝ)
    (hf : ∀ j, ‖f j‖ ≤ C) :
    ‖gnsFamily τ f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
  rw [norm_gnsFamily_sq]
  calc
    _ ≤ ∑ _ : ι, C ^ 2 := by
      apply sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) ((preGNS_norm_le τ h1 _).trans (hf j)) _
    _ = _ := by simp

lemma norm_gnsFamily_square_card_le (h1 : τ 1 = 1) {K : ℕ} [NeZero K]
    (f : ZMod (K ^ 2) → A) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ j, ‖f j‖ ≤ C / (K : ℝ) ^ 2) :
    ‖gnsFamily τ f‖ ≤ C / (K : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))).mp
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  calc
    _ ≤ (Fintype.card (ZMod (K ^ 2)) : ℝ) * (C / (K : ℝ) ^ 2) ^ 2 :=
      norm_gnsFamily_sq_le τ h1 f _ hf
    _ = _ := by rw [ZMod.card, Nat.cast_pow]; field_simp

lemma norm_gnsFamily_harmonic_error_le (h1 : τ 1 = 1) {K : ℕ} [NeZero K]
    (q : ZMod (K ^ 2) → A) (v : ZMod (K ^ 2) → unitary A)
    (hv : ∀ j, ‖(v j : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2) (n : ℕ) :
    ‖gnsFamily τ (fun j => harmonicPolynomial n (v j : A) * q j -
        (harmonic n : ℂ) • q j)‖ ≤ (2 * n : ℝ) / (K : ℝ) := by
  apply norm_gnsFamily_square_card_le τ h1 _ _ (by positivity)
  intro j
  calc
    _ ≤ (n : ℝ) * ‖(v j : A) * q j - q j‖ := norm_harmonicPolynomial_mul_sub_le _ _ _
    _ ≤ (n : ℝ) * (2 / (K : ℝ) ^ 2) := by gcongr; exact hv j
    _ = _ := by ring

 

theorem unitary_power_multiplier_bound [Nontrivial A]
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (S : A →L[ℂ] A) (u : unitary A) (a b : A)
    (hpos : ∀ k : ℕ, 0 < k → S ((u : A) ^ k) = a * (u : A) ^ k)
    (hneg : ∀ k : ℕ, 0 < k → S ((star u : A) ^ k) = b * (star u : A) ^ k)
    (n : ℕ) {K : ℕ} [NeZero K] :
    (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤
      (2 * (1 + Real.pi)) * ‖S‖ + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / K) := by
  let q : ZMod (K ^ 2) → A := fun j => fourierWindow (u : A) j
  let v : ZMod (K ^ 2) → unitary A := fun j => rootUnitary (-j) • u
  have hvdef (j) : (v j : A) = (ZMod.stdAddChar (-j)) • (u : A) := rfl
  have hq : ∑ j, q j * star (q j) = 1 := sum_fourierWindow_mul_star u
  have hv (j) : ‖(v j : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    simpa only [q, v, Nat.cast_pow] using norm_unitary_mul_fourierWindow_sub_le u j
  have hvneg (j) : ‖(star (v j) : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    rw [norm_star_unitary_mul_sub]
    exact hv j
  let ep := fun j => harmonicPolynomial n (v j : A) * q j - (harmonic n : ℂ) • q j
  let em := fun j => star (harmonicPolynomial n (v j : A)) * q j - (harmonic n : ℂ) • q j
  let F := fun j => S (harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A)))
  have hep : ‖gnsFamily τ ep‖ ≤ (2 * n : ℝ) / K :=
    norm_gnsFamily_harmonic_error_le τ h1 q v hv n
  have hem : ‖gnsFamily τ em‖ ≤ (2 * n : ℝ) / K := by
    simpa only [em, star_harmonicPolynomial, Unitary.coe_star] using
      norm_gnsFamily_harmonic_error_le τ h1 q (fun j => star (v j)) hvneg n
  have hF (j) : F j = a * harmonicPolynomial n (v j : A) -
      b * star (harmonicPolynomial n (v j : A)) := by
    have hp : ∀ k : ℕ, 0 < k → S ((v j : A) ^ k) = a * (v j : A) ^ k := by
      simpa only [hvdef] using power_multiplier_smul S (u : A) a hpos (ZMod.stdAddChar (-j))
    have hn : ∀ k : ℕ, 0 < k → S (star (v j : A) ^ k) = b * star (v j : A) ^ k := by
      simpa only [hvdef, star_smul] using
        power_multiplier_smul S (star u : A) b hneg (star (ZMod.stdAddChar (-j)))
    simp only [F, map_sub, star_harmonicPolynomial]
    rw [map_harmonicPolynomial S _ a hp, map_harmonicPolynomial S _ b hn]
  have hFbound (j) : ‖F j‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    calc
      _ ≤ ‖S‖ * ‖harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A))‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (2 * (1 + Real.pi)) := by
        gcongr
        exact norm_unitary_harmonicPolynomial_sub_star_le (v j) n
      _ = _ := mul_comm _ _
  have hqn : ‖gnsFamily τ q‖ = 1 := by
    simpa only [one_mul, preGNS_norm_one τ h1] using norm_gnsFamily_mul τ htr q hq 1
  have hFn : ‖gnsFamily τ (fun j => F j * q j)‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    simpa only [hqn, mul_one] using
      norm_gnsFamily_leftMul_le τ F q _ (by positivity) hFbound
  have hepn : ‖gnsFamily τ (fun j => a * ep j)‖ ≤ ‖a‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => a) ep ‖a‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hemn : ‖gnsFamily τ (fun j => b * em j)‖ ≤ ‖b‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => b) em ‖b‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hid (j) : (harmonic n : ℂ) • ((a - b) * q j) =
      F j * q j - a * ep j + b * em j := by
    simp only [hF j, ep, em, sub_mul, mul_sub, smul_sub, mul_smul_comm]
    noncomm_ring
  have hh : 0 ≤ (harmonic n : ℝ) := by unfold harmonic; positivity
  have hhnorm : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_of_nonneg hh]
  calc
    _ = ‖gnsFamily τ (fun j => (harmonic n : ℂ) • ((a - b) * q j))‖ := by
      rw [gnsFamily_smul, norm_smul, hhnorm, norm_gnsFamily_mul τ htr q hq]
    _ = ‖gnsFamily τ (fun j => F j * q j) - gnsFamily τ (fun j => a * ep j) +
        gnsFamily τ (fun j => b * em j)‖ := by
      simp only [hid, gnsFamily_add, gnsFamily_sub]
    _ ≤ (‖gnsFamily τ (fun j => F j * q j)‖ + ‖gnsFamily τ (fun j => a * ep j)‖) +
        ‖gnsFamily τ (fun j => b * em j)‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ _ := by nlinarith [hFn, hepn, hemn]

 

theorem unitary_power_rigidity
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (hfaithful : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (S : A →L[ℂ] A) (u : unitary A) (a b : A)
    (hpos : ∀ k : ℕ, 0 < k → S ((u : A) ^ k) = a * (u : A) ^ k)
    (hneg : ∀ k : ℕ, 0 < k → S ((star u : A) ^ k) = b * (star u : A) ^ k) :
    a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let C : ℝ := (2 * (1 + Real.pi)) * ‖S‖
  have hbound (n : ℕ) : (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤ C := by
    have hl : Filter.Tendsto (fun m : ℕ =>
        C + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / ((m : ℝ) + 1)))
        Filter.atTop (nhds C) := by
      simpa only [mul_zero, add_zero, mul_one_div] using
        tendsto_const_nhds.add
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (n : ℝ)) |>.const_mul (‖a‖ + ‖b‖))
    apply ge_of_tendsto hl
    apply Filter.Eventually.of_forall
    intro m
    simpa only [Nat.cast_add, Nat.cast_one] using
      unitary_power_multiplier_bound τ h1 htr S u a b hpos hneg n (K := m + 1)
  have hdiv : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono log_add_one_le_harmonic
      (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
          Filter.atTop Filter.atTop).comp (Filter.tendsto_add_atTop_nat 1)))
  have hz : ‖τ.toPreGNS (a - b)‖ = 0 := by
    by_contra hne
    have hp : 0 < ‖τ.toPreGNS (a - b)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := ((hdiv.atTop_mul_const hp).eventually_gt_atTop C).exists
    exact (not_lt_of_ge (hbound n)) hn
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaithful (a - b)).mp hz)

end TraceHilbertSpace

end HochschildRigidity
end

end OAI
