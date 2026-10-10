import OAI.Analysis.OInfinity.CARCombination

namespace OAI

/-! # Finite geometric modes for the binary corner shift

A normalized geometric block has a shift error at its two endpoints only.
The squared coefficient error is exactly `2 / L`; the CAR norm
estimate transfers it to actual elements of the C*-algebra. Blocks whose
index intervals are disjoint have zero mixed anticommutator.
The shift here is `x ↦ a*x*star a + b*x*star b` for a relative Cuntz pair.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

def carModeScale (L : ℕ) : ℝ := (Real.sqrt (L : ℝ))⁻¹

def carModeCoefficient (L : ℕ) (ζ : ℂ) (k : ℕ) : ℂ :=
  (carModeScale L : ℂ) * star ζ ^ k

lemma carModeScale_nonneg (L : ℕ) : 0 ≤ carModeScale L := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma carModeScale_normalized (L : ℕ) (hL : 0 < L) :
    (L : ℝ) * carModeScale L ^ 2 = 1 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : Real.sqrt (L : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hLr)
  have hsquare := Real.sq_sqrt hLr.le
  unfold carModeScale
  field_simp
  nlinarith

lemma carModeScale_sq (L : ℕ) (hL : 0 < L) :
    carModeScale L ^ 2 = 1 / (L : ℝ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  apply (eq_div_iff (ne_of_gt hLr)).mpr
  nlinarith [carModeScale_normalized L hL]

lemma carModeCoefficient_norm (L : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (k : ℕ) :
    ‖carModeCoefficient L ζ k‖ = carModeScale L := by
  simp only [carModeCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (carModeScale_nonneg L), norm_pow, norm_star, hζ, one_pow, mul_one]

lemma carModeCoefficient_step (L : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (k : ℕ) :
    ζ * carModeCoefficient L ζ (k + 1) = carModeCoefficient L ζ k := by
  have hunit : ζ * star ζ = 1 := by
    simpa only [Complex.star_def, hζ, one_pow, Complex.ofReal_one] using Complex.mul_conj' ζ
  unfold carModeCoefficient
  rw [pow_succ]
  calc
    _ = (carModeScale L : ℂ) * star ζ ^ k * (ζ * star ζ) := by ring
    _ = _ := by rw [hunit, mul_one]

lemma carModeCoefficient_norm_sq_sum (L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∑ i : Fin L, ‖carModeCoefficient L ζ i.val‖ ^ 2) = 1 := by
  simp only [carModeCoefficient_norm L ζ hζ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact carModeScale_normalized L hL

lemma carModeCoefficient_inner_self (L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∑ i : Fin L, star (carModeCoefficient L ζ i.val) *
      carModeCoefficient L ζ i.val) = 1 := by
  have hterm (i : Fin L) : star (carModeCoefficient L ζ i.val) *
      carModeCoefficient L ζ i.val = ((carModeScale L ^ 2 : ℝ) : ℂ) := by
    have h : star (carModeCoefficient L ζ i.val) * carModeCoefficient L ζ i.val =
        ((‖carModeCoefficient L ζ i.val‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.ofReal_pow] using
        Complex.conj_mul' (carModeCoefficient L ζ i.val)
    simpa only [carModeCoefficient_norm L ζ hζ] using h
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact_mod_cast carModeScale_normalized L hL

def carModeInitialCoefficient (L : ℕ) (ζ : ℂ) (i : Fin (L + 1)) : ℂ :=
  if i.val < L then carModeCoefficient L ζ i.val else 0

def carModeShiftCoefficient (L : ℕ) (ζ : ℂ) (i : Fin (L + 1)) : ℂ :=
  if i.val = 0 then 0 else carModeCoefficient L ζ (i.val - 1)

lemma carModeCoefficient_endpoint_error (L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (i : Fin (L + 1)) :
    carModeShiftCoefficient L ζ i - ζ * carModeInitialCoefficient L ζ i =
      if i.val = 0 then -(ζ * (carModeScale L : ℂ))
      else if i.val = L then carModeCoefficient L ζ (L - 1) else 0 := by
  by_cases hzero : i.val = 0
  · simp only [carModeShiftCoefficient, carModeInitialCoefficient, hzero, ite_true,
      hL, carModeCoefficient, pow_zero, mul_one, zero_sub]
  · by_cases hlast : i.val = L
    · have hLne : L ≠ 0 := by omega
      simp only [carModeShiftCoefficient, carModeInitialCoefficient, hlast, hLne,
        ite_false, lt_self_iff_false, mul_zero, sub_zero, ite_true]
    · have hi : i.val < L := by omega
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hstep : ζ * carModeCoefficient L ζ i.val =
          carModeCoefficient L ζ (i.val - 1) := by
        simpa only [hpred] using carModeCoefficient_step L ζ hζ (i.val - 1)
      simp only [carModeShiftCoefficient, carModeInitialCoefficient, hzero, hlast,
        hi, ite_false, ite_true, hstep, sub_self]

/-- The error has two coefficients of equal modulus, with no interior contribution. -/
lemma carModeCoefficient_error_sq_sum (L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∑ i : Fin (L + 1),
      ‖carModeShiftCoefficient L ζ i - ζ * carModeInitialCoefficient L ζ i‖ ^ 2) =
      2 / (L : ℝ) := by
  have hends : (0 : Fin (L + 1)) ≠ Fin.last L := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hpoint (i : Fin (L + 1)) :
      ‖carModeShiftCoefficient L ζ i - ζ * carModeInitialCoefficient L ζ i‖ ^ 2 =
        (if i = 0 then carModeScale L ^ 2 else 0) +
          (if i = Fin.last L then carModeScale L ^ 2 else 0) := by
    rw [carModeCoefficient_endpoint_error L hL ζ hζ i]
    by_cases hzero : i = 0
    · subst i
      simp only [Fin.val_zero, ite_true, hends, ite_false, add_zero, norm_neg,
        norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (carModeScale_nonneg L), one_mul]
    · by_cases hlast : i = Fin.last L
      · subst i
        have hLne : L ≠ 0 := by omega
        simp only [Fin.val_last, hLne, ite_false, ite_true, hzero, zero_add,
          carModeCoefficient_norm L ζ hζ]
      · have hzero' : i.val ≠ 0 := by
          intro h
          exact hzero (Fin.ext h)
        have hlast' : i.val ≠ L := by
          intro h
          exact hlast (Fin.ext h)
        simp only [hzero', hlast', hzero, hlast, ite_false, norm_zero, add_zero]
        norm_num
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [carModeScale_sq L hL]
  ring

variable {E : Type*} [CStarAlgebra E]

private lemma carSynthesis_cross_mul {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (y : J → E) (c : I → ℂ) (d : J → ℂ) :
    carSynthesis x c * carSynthesis y d =
      ∑ i, ∑ j, (c i * d j) • (x i * y j) := by
  unfold carSynthesis
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

private lemma carSynthesis_cross_anticommute {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (y : J → E) (hxy : ∀ i j, x i * y j + y j * x i = 0)
    (c : I → ℂ) (d : J → ℂ) :
    carSynthesis x c * carSynthesis y d + carSynthesis y d * carSynthesis x c = 0 := by
  have hswap : carSynthesis y d * carSynthesis x c =
      ∑ i, ∑ j, (c i * d j) • (y j * x i) := by
    rw [carSynthesis_cross_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (d j)]
  rw [carSynthesis_cross_mul, hswap, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, hxy, smul_zero]
  simp only [Finset.sum_const_zero]

def carGeometricMode (a b : E) (start L : ℕ) (ζ : ℂ) : E :=
  carSynthesis (fun i : Fin L => zeroCornerCAR a b (start + i.val))
    (fun i => carModeCoefficient L ζ i.val)

def carGeometricShift (a b : E) (start L : ℕ) (ζ : ℂ) : E :=
  carSynthesis (fun i : Fin L => zeroCornerCAR a b (start + i.val + 1))
    (fun i => carModeCoefficient L ζ i.val)

lemma carGeometricMode_as_synthesis (a b : E) (start L : ℕ) (ζ : ℂ) :
    carGeometricMode a b start L ζ =
      carSynthesis (fun i : Fin (L + 1) => zeroCornerCAR a b (start + i.val))
        (carModeInitialCoefficient L ζ) := by
  unfold carGeometricMode carSynthesis
  rw [Fin.sum_univ_castSucc]
  simp only [carModeInitialCoefficient, Fin.val_castSucc, Fin.isLt, ite_true,
    Fin.val_last, lt_self_iff_false, ite_false, zero_smul, add_zero]

lemma carGeometricShift_as_synthesis (a b : E) (start L : ℕ) (ζ : ℂ) :
    carGeometricShift a b start L ζ =
      carSynthesis (fun i : Fin (L + 1) => zeroCornerCAR a b (start + i.val))
        (carModeShiftCoefficient L ζ) := by
  unfold carGeometricShift carSynthesis
  rw [Fin.sum_univ_succ]
  simp only [carModeShiftCoefficient, Fin.val_zero, ite_true, zero_smul, zero_add,
    Fin.val_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
    Nat.add_assoc]

section Corner
variable (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
  (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
  (hsum : a * star a + b * star b = q)

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_gram (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    star (carGeometricMode a b start L ζ) * carGeometricMode a b start L ζ +
      carGeometricMode a b start L ζ * star (carGeometricMode a b start L ζ) = q := by
  have hf : Function.Injective (fun i : Fin L => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have hcar (i j : Fin L) :
      star (zeroCornerCAR a b (start + i.val)) * zeroCornerCAR a b (start + j.val) +
        zeroCornerCAR a b (start + j.val) * star (zeroCornerCAR a b (start + i.val)) =
          if i = j then q else 0 := by
    simpa only [hf.eq_iff] using
      zeroCornerCAR_star_anticommute q a b hqstar hqq haa hbb hab hsum
        (start + i.val) (start + j.val)
  have h := carSynthesis_star_anticommute q
    (fun i : Fin L => zeroCornerCAR a b (start + i.val)) hcar
    (fun i => carModeCoefficient L ζ i.val) (fun i => carModeCoefficient L ζ i.val)
  simpa only [carGeometricMode, carModeCoefficient_inner_self L hL ζ hζ, one_smul] using h

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_norm_le_one (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) : ‖carGeometricMode a b start L ζ‖ ≤ 1 := by
  have hf : Function.Injective (fun i : Fin L => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have h := zeroCornerCAR_synthesis_norm_sq_le q a b hqstar hqq haa hbb hab hsum
    (fun i : Fin L => start + i.val) hf (fun i => carModeCoefficient L ζ i.val)
  rw [carModeCoefficient_norm_sq_sum L hL ζ hζ] at h
  change ‖carGeometricMode a b start L ζ‖ * ‖carGeometricMode a b start L ζ‖ ≤ 1 at h
  nlinarith [norm_nonneg (carGeometricMode a b start L ζ)]

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_anticommute (start stop L K : ℕ) (ζ μ : ℂ) :
    carGeometricMode a b start L ζ * carGeometricMode a b stop K μ +
      carGeometricMode a b stop K μ * carGeometricMode a b start L ζ = 0 := by
  apply carSynthesis_cross_anticommute
  intro i j
  exact zeroCornerCAR_anticommute q a b hqstar hqq haa hbb hab hsum _ _

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_disjoint_star_anticommute (start stop L K : ℕ)
    (hdisjoint : start + L ≤ stop ∨ stop + K ≤ start) (ζ μ : ℂ) :
    star (carGeometricMode a b start L ζ) * carGeometricMode a b stop K μ +
      carGeometricMode a b stop K μ * star (carGeometricMode a b start L ζ) = 0 := by
  unfold carGeometricMode
  rw [carSynthesis_star]
  apply carSynthesis_cross_anticommute
  intro i j
  have hij : start + i.val ≠ stop + j.val := by
    have hi := i.isLt
    have hj := j.isLt
    rcases hdisjoint with h | h <;> omega
  simpa only [hij, ite_false] using
    zeroCornerCAR_star_anticommute q a b hqstar hqq haa hbb hab hsum
      (start + i.val) (stop + j.val)

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_shift_error (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖carGeometricShift a b start L ζ - ζ • carGeometricMode a b start L ζ‖ *
      ‖carGeometricShift a b start L ζ - ζ • carGeometricMode a b start L ζ‖ ≤
        2 / (L : ℝ) := by
  let x : Fin (L + 1) → E := fun i => zeroCornerCAR a b (start + i.val)
  let c : Fin (L + 1) → ℂ := fun i =>
    carModeShiftCoefficient L ζ i - ζ * carModeInitialCoefficient L ζ i
  have hrepr : carGeometricShift a b start L ζ - ζ • carGeometricMode a b start L ζ =
      carSynthesis x c := by
    rw [carGeometricShift_as_synthesis, carGeometricMode_as_synthesis]
    simp only [x, c, carSynthesis, sub_smul, Finset.sum_sub_distrib,
      Finset.smul_sum, smul_smul]
  rw [hrepr]
  have hf : Function.Injective (fun i : Fin (L + 1) => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have h := zeroCornerCAR_synthesis_norm_sq_le q a b hqstar hqq haa hbb hab hsum
    (fun i : Fin (L + 1) => start + i.val) hf c
  simpa only [x, c, carModeCoefficient_error_sq_sum L hL ζ hζ] using h

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerCAR_shift_single (n : ℕ) :
    zeroCornerShift a b (zeroCornerCAR a b n) =
      zeroCornerParity a b * zeroCornerCAR a b (n + 1) := by
  change _ = zeroCornerParity a b *
    (zeroCornerParity a b * zeroCornerShift a b (zeroCornerCAR a b n))
  rw [← mul_assoc, zeroCornerParity_sq q a b hqstar hqq haa hbb hab hsum,
    (zeroCornerShift_support q a b hqstar hqq haa hbb hab hsum _).1]

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_shift (start L : ℕ) (ζ : ℂ) :
    zeroCornerShift a b (carGeometricMode a b start L ζ) =
      zeroCornerParity a b * carGeometricShift a b start L ζ := by
  unfold carGeometricMode carGeometricShift carSynthesis
  rw [zeroCornerShift_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [zeroCornerShift_smul,
    zeroCornerCAR_shift_single q a b hqstar hqq haa hbb hab hsum,
    mul_smul_comm]

include hqstar hqq haa hbb hab hsum in
lemma zeroCornerParity_norm_le_one : ‖zeroCornerParity a b‖ ≤ 1 := by
  have hqnorm : ‖q‖ ≤ 1 := by
    have h : ‖star q * q‖ = ‖q‖ * ‖q‖ := CStarRing.norm_star_mul_self
    rw [hqstar, hqq] at h
    nlinarith [norm_nonneg q]
  have h : ‖star (zeroCornerParity a b) * zeroCornerParity a b‖ =
      ‖zeroCornerParity a b‖ * ‖zeroCornerParity a b‖ := CStarRing.norm_star_mul_self
  rw [zeroCornerParity_star, zeroCornerParity_sq q a b hqstar hqq haa hbb hab hsum] at h
  nlinarith [norm_nonneg (zeroCornerParity a b)]

include hqstar hqq haa hbb hab hsum in
lemma carGeometricMode_twisted_shift_error (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖zeroCornerShift a b (carGeometricMode a b start L ζ) -
        zeroCornerParity a b * (ζ • carGeometricMode a b start L ζ)‖ ^ 2 ≤
      2 / (L : ℝ) := by
  let d := carGeometricShift a b start L ζ - ζ • carGeometricMode a b start L ζ
  have heq : zeroCornerShift a b (carGeometricMode a b start L ζ) -
      zeroCornerParity a b * (ζ • carGeometricMode a b start L ζ) =
        zeroCornerParity a b * d := by
    rw [carGeometricMode_shift q a b hqstar hqq haa hbb hab hsum]
    exact (mul_sub _ _ _).symm
  have hn : ‖zeroCornerParity a b * d‖ ≤ ‖d‖ :=
    (norm_mul_le _ _).trans (by
      nlinarith [zeroCornerParity_norm_le_one q a b hqstar hqq haa hbb hab hsum,
        norm_nonneg d])
  have herr := carGeometricMode_shift_error q a b hqstar hqq haa hbb hab hsum
    start L hL ζ hζ
  rw [heq]
  change ‖d‖ * ‖d‖ ≤ 2 / (L : ℝ) at herr
  nlinarith [norm_nonneg (zeroCornerParity a b * d), norm_nonneg d]

end Corner
end WeakPureInfiniteness

end

end OAI
