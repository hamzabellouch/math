import OAI.Analysis.Steinitz.Gain

namespace OAI

/-! Filtered coefficients and their quadratic energy bounds. -/

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_controls_gain {Z V : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) {q : ℝ} (hq : 0 ≤ q)
    (hG : relativeMoment (1 + Z) V ≤ q ^ exponent) :
    V ≤ q • (1 + Z) := by
  have hS : ((1 : Matrix ι ι ℝ) + Z).PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hA := trace_power_bound (sandwich_psd hV (1 + Z)) exponent_pos hq hG
  have h := congruence_mono hA (CFC.sqrt (1 + Z))
  rw [sqrt_transpose] at h
  have he : CFC.sqrt (1 + Z) * (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z)) *
      CFC.sqrt (1 + Z) = V := by
    simp only [← Matrix.mul_assoc, sqrt_mul_inverseSqrt hS, Matrix.one_mul]
    rw [Matrix.mul_assoc, inverseSqrt_mul_sqrt hS, Matrix.mul_one]
  rw [he] at h
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg] using h

lemma accumulated_gain_bound {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ}
    (hcost : gainCost Y ps ≤ E) (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let q := (gainConstant * E) ^ (1 / exponent)
    0 ≤ q ∧ q < 1 / 4 ∧
    (follow Y 0 ps).2 ≤ q • (1 + (follow Y 0 ps).1) ∧
    (follow Y 0 ps).2 ≤ q • (1 + ((follow Y 0 ps).1 + (follow Y 0 ps).2)) := by
  have hE : 0 ≤ E := (gainCost_nonneg hY hp).trans hcost
  have hc : 0 ≤ gainConstant * E := mul_nonneg gainConstant_pos.le hE
  have hce : gainConstant * E ≤ 1 / 16 := by
    have hd := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) gainConstant_pos)).mp hsmall
    nlinarith
  let q := (gainConstant * E) ^ (1 / exponent)
  have hq : 0 ≤ q := Real.rpow_nonneg hc _
  have hpow : q ^ exponent = gainConstant * E := by
    dsimp only [q]
    rw [← Real.rpow_mul hc]
    rw [one_div_mul_cancel (ne_of_gt exponent_pos), Real.rpow_one]
  have hquarter : (1 / 16 : ℝ) < (1 / 4 : ℝ) ^ exponent := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    norm_num [exponent, Real.rpow_natCast]
  have hqsmall : q < 1 / 4 := by
    apply (Real.rpow_lt_rpow_iff hq (by norm_num) exponent_pos).mp
    rw [hpow]
    exact hce.trans_lt hquarter
  have hb : relativeMoment (1 + Y) 0 + gainConstant * gainCost (Y + 0) ps ≤ 1 / 4 := by
    rw [relativeMoment_zero, zero_add, add_zero]
    have hh := mul_le_mul_of_nonneg_left hcost gainConstant_pos.le
    linarith
  have hg := relativeMoment_path hY Matrix.PosSemidef.zero hp hb
  rw [relativeMoment_zero, zero_add, add_zero] at hg
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hG : relativeMoment (1 + (follow Y 0 ps).1) (follow Y 0 ps).2 ≤ q ^ exponent := by
    rw [hpow]
    exact hg.trans (mul_le_mul_of_nonneg_left hcost gainConstant_pos.le)
  have hbound := relativeMoment_controls_gain hpsd.1 hpsd.2 hq hG
  refine ⟨hq, hqsmall, hbound, hbound.trans ?_⟩
  apply smul_le_smul_of_nonneg_left _ hq
  exact add_le_add le_rfl (le_add_of_nonneg_right hpsd.2.nonneg)

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.PotentialScalar
open MatrixEnergy

noncomputable def rate (x : ℝ) : ℝ := min (Real.sqrt x) ((max 1 x)⁻¹ ^ 2)
noncomputable def primitive (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..x, rate u

lemma continuous_rate : Continuous rate := by
  unfold rate
  apply Continuous.min Real.continuous_sqrt
  apply Continuous.pow
  apply Continuous.inv₀ (continuous_const.max continuous_id)
  intro x
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))

lemma rate_nonneg (x : ℝ) : 0 ≤ rate x := le_min (Real.sqrt_nonneg _) (sq_nonneg _)

lemma rate_small {x : ℝ} (hx : x ≤ 1) : rate x = Real.sqrt x := by
  unfold rate
  rw [max_eq_left hx]
  norm_num only [inv_one, one_pow]
  exact min_eq_left (Real.sqrt_le_one.mpr hx)

lemma rate_large {x : ℝ} (hx : 1 ≤ x) : rate x = x⁻¹ ^ 2 := by
  unfold rate
  rw [max_eq_right hx]
  apply min_eq_right
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have his : x⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hx0.le) hi
  exact his.trans (Real.one_le_sqrt.mpr hx)

lemma rate_eq {x : ℝ} (hx : 0 ≤ x) : rate x = weight x / x := by
  by_cases h1 : x ≤ 1
  · rw [rate_small h1, integrand_of_le_one hx h1, Real.sqrt_eq_rpow]
  · have h1' : 1 ≤ x := (lt_of_not_ge h1).le
    rw [rate_large h1', integrand_of_one_le h1']
    rw [show (-2 : ℝ) = -1 * 2 by norm_num, Real.rpow_mul hx, Real.rpow_neg_one,
      Real.rpow_two]

lemma rate_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : rate x = 0 := by
  rw [rate_small (hx.trans (by norm_num)), Real.sqrt_eq_zero_of_nonpos hx]

lemma primitive_eq {x : ℝ} (hx : 0 ≤ x) : primitive x = potential x := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hx] at hu
  exact rate_eq hu.1

lemma primitive_derivative (x : ℝ) : HasDerivAt primitive (rate x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_rate.intervalIntegrable 0 x)
    continuous_rate.stronglyMeasurable.stronglyMeasurableAtFilter continuous_rate.continuousAt

lemma primitive_monotone : Monotone primitive := by
  apply monotone_of_hasDerivAt_nonneg primitive_derivative
  exact rate_nonneg

lemma primitive_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : primitive x = 0 := by
  unfold primitive
  calc
    _ = ∫ u in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_ge hx] at hu
      exact rate_zero_of_nonpos hu.2
    _ = 0 := by simp

lemma large_add_linear_monotone : MonotoneOn (fun x : ℝ => x⁻¹ ^ 2 + 2 * x) (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (f' := fun x => -2 * x⁻¹ ^ 3 + 2)
  · have hne : ∀ x ∈ Set.Ici (1 : ℝ), x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)
    exact (((continuousOn_id.inv₀ hne).pow 2).add
      (continuous_const.mul continuous_id).continuousOn)
  · intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hxn : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
    have h := (((hasDerivAt_id x).inv hxn).fun_pow 2).fun_add (hasDerivAt_const_mul (x := x) 2)
    convert! h.hasDerivWithinAt using 1
    simp
    ring
  · intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
    have hp : x⁻¹ ^ 3 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) hi
    linarith

lemma rate_add_linear_monotone : Monotone (fun x : ℝ => rate x + 2 * x) := by
  intro x y hxy
  change rate x + 2 * x ≤ rate y + 2 * y
  by_cases hx : x ≤ 1
  · by_cases hy : y ≤ 1
    · rw [rate_small hx, rate_small hy]
      exact add_le_add (Real.sqrt_le_sqrt hxy) (by linarith)
    · have hy' : 1 ≤ y := (lt_of_not_ge hy).le
      have hl : rate x + 2 * x ≤ 3 := by
        rw [rate_small hx]
        have hs := Real.sqrt_le_one.mpr hx
        linarith
      have hr := large_add_linear_monotone (show (1 : ℝ) ≤ 1 by norm_num) hy' hy'
      rw [rate_large hy']
      norm_num only [inv_one, one_pow, mul_one, show (1 : ℝ) + 2 = 3 by norm_num] at hr
      exact hl.trans hr
  · have hx' : 1 ≤ x := (lt_of_not_ge hx).le
    have hy' := hx'.trans hxy
    rw [rate_large hx', rate_large hy']
    exact large_add_linear_monotone hx' hy' hxy

lemma convexified_derivative (x : ℝ) :
    HasDerivAt (fun u : ℝ => primitive u + u ^ 2) (rate x + 2 * x) x := by
  simpa using! (primitive_derivative x).fun_add ((hasDerivAt_id x).fun_pow 2)

lemma convexified_convex : ConvexOn ℝ Set.univ (fun x : ℝ => primitive x + x ^ 2) := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (convexified_derivative x).differentiableAt)
  have he : deriv (fun x : ℝ => primitive x + x ^ 2) = (fun x => rate x + 2 * x) := by
    funext x
    exact (convexified_derivative x).deriv
  rw [he]
  exact rate_add_linear_monotone

end EuclideanSteinitz.PotentialScalar

namespace EuclideanSteinitz.PotentialScalar
open MatrixEnergy

lemma sizeWeight_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : sizeWeight x = Real.sqrt x := by
  rw [sizeWeight, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · apply min_eq_left
    exact (Real.sqrt_le_one.mpr hx1).trans ((one_le_inv₀ hx).mpr hx1)

lemma sizeWeight_large {x : ℝ} (hx : 1 ≤ x) : sizeWeight x = x⁻¹ := by
  rw [sizeWeight, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  exact min_eq_right ((inv_le_one_of_one_le₀ hx).trans (Real.one_le_sqrt.mpr hx))

lemma primitive_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    primitive x = (2 / 3 : ℝ) * x * Real.sqrt x := by
  rw [primitive_eq hx, potential_small hx hx1,
    show exponent = (1 / 2 : ℝ) + 1 by norm_num [exponent],
    Real.rpow_add_one' hx (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0), ← Real.sqrt_eq_rpow]
  ring

lemma primitive_nonneg (x : ℝ) : 0 ≤ primitive x := by
  by_cases hx : 0 ≤ x
  · have h := primitive_monotone hx
    simpa only [primitive_zero_of_nonpos (le_refl (0 : ℝ))] using h
  · rw [primitive_zero_of_nonpos (le_of_not_ge hx)]

lemma primitive_sub_le {x z M : ℝ} (hzx : z ≤ x)
    (hM : ∀ u ∈ Set.Icc z x, rate u ≤ M) : primitive x - primitive z ≤ (x - z) * M := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (continuous_rate.intervalIntegrable 0 z) (continuous_rate.intervalIntegrable z x)
  have hi := intervalIntegral.integral_mono_on hzx (continuous_rate.intervalIntegrable z x)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume z x) hM
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  unfold primitive
  linarith

lemma rate_le_inverse_sq {u : ℝ} (hu : 0 < u) : rate u ≤ u⁻¹ ^ 2 := by
  apply (min_le_right _ _).trans
  exact pow_le_pow_left₀ (by positivity)
    (inv_le_inv₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 u)) hu |>.mpr
      (le_max_right _ _)) 2

lemma direct_scalar_bound {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4) :
    primitive x - primitive ((1 - q) * x - q) ≤ 8 * q * sizeWeight x := by
  let z := (1 - q) * x - q
  have hzx : z ≤ x := by dsimp [z]; nlinarith
  have hd : x - z = q * (1 + x) := by dsimp [z]; ring
  by_cases hsmall : x ≤ 4 * q
  · have hx1 : x ≤ 1 := by linarith
    rw [sizeWeight_small hx hx1, primitive_small hx hx1]
    have hp := primitive_nonneg z
    have hm := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg x)
    have hqs := mul_nonneg hq (Real.sqrt_nonneg x)
    change _ - primitive z ≤ _
    nlinarith
  · have hlarge : 4 * q < x := lt_of_not_ge hsmall
    have hx0 : 0 < x := by linarith
    have hhalf : x / 2 ≤ z := by
      dsimp [z]
      have hqx := mul_le_mul_of_nonneg_right hq1 hx
      nlinarith
    by_cases hx1 : x ≤ 1
    · have hi := primitive_sub_le hzx (M := Real.sqrt x) (fun u hu =>
        (min_le_left _ _).trans (Real.sqrt_le_sqrt hu.2))
      rw [hd] at hi
      rw [sizeWeight_small hx hx1]
      have hm := mul_le_mul_of_nonneg_left hx1 hq
      have hs := Real.sqrt_nonneg x
      change _ - primitive z ≤ _
      nlinarith [mul_nonneg (by linarith : 0 ≤ 8 * q - q * (1 + x)) hs]
    · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
      have hrate : ∀ u ∈ Set.Icc z x, rate u ≤ 4 * x⁻¹ ^ 2 := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le (by linarith : 0 < x / 2) (hhalf.trans hu.1)
        have hi : u⁻¹ ≤ 2 * x⁻¹ := by
          calc
            u⁻¹ ≤ (x / 2)⁻¹ := (inv_le_inv₀ hu0 (half_pos hx0)).mpr (hhalf.trans hu.1)
            _ = 2 * x⁻¹ := by simp [div_eq_mul_inv]
        have hh := pow_le_pow_left₀ (inv_nonneg.mpr hu0.le) hi 2
        exact (rate_le_inverse_sq hu0).trans (by nlinarith)
      have hi := primitive_sub_le hzx hrate
      rw [hd] at hi
      rw [sizeWeight_large hx1']
      change _ - primitive z ≤ _
      have he : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx0)
      have him : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1'
      have hin : 0 ≤ x⁻¹ := inv_nonneg.mpr hx
      have hs : x * x⁻¹ ^ 2 = x⁻¹ := by calc
        _ = (x * x⁻¹) * x⁻¹ := by ring
        _ = x⁻¹ := by rw [he, one_mul]
      have hsq : x⁻¹ ^ 2 ≤ x⁻¹ := by nlinarith
      have hc := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hq)
      nlinarith

end EuclideanSteinitz.PotentialScalar

namespace EuclideanSteinitz.Spectral
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_primitive_monotone {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (_hB : B.IsHermitian) (hAB : A ≤ B) :
    (cfc PotentialScalar.primitive A).trace ≤ (cfc PotentialScalar.primitive B).trace := by
  have hH := Matrix.le_iff.mp hAB
  have hd (t : ℝ) := trace_semiconvex_affine_derivative hA hH.1
    PotentialScalar.primitive PotentialScalar.rate PotentialScalar.continuous_rate
    PotentialScalar.primitive_derivative PotentialScalar.convexified_convex t
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by
    apply MatrixEnergy.trace_mul_nonneg _ hH
    apply Matrix.nonneg_iff_posSemidef.mp
    exact cfc_nonneg (fun x _ => PotentialScalar.rate_nonneg x))
  have h := hm (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using h

lemma cfc_primitive_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    cfc PotentialScalar.primitive A = cfc potential A := by
  apply cfc_congr
  intro x hx
  exact PotentialScalar.primitive_eq (spectrum_nonneg_of_nonneg hA.nonneg hx)

lemma trace_potential_direct {X Z : Matrix ι ι ℝ} (hX : X.PosSemidef) (hZ : Z.PosSemidef)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4)
    (hXZ : X - Z ≤ q • (1 + X)) :
    (cfc potential X).trace - (cfc potential Z).trace ≤ 8 * q * (cfc sizeWeight X).trace := by
  let A : Matrix ι ι ℝ := (1 - q) • X - q • 1
  have hA : A.IsHermitian := (hX.1.smul (IsSelfAdjoint.all _)).sub (isHermitian_one.smul (IsSelfAdjoint.all _))
  have hAZ : A ≤ Z := by
    apply Matrix.le_iff.mpr
    have hh := Matrix.le_iff.mp hXZ
    convert! hh using 1
    dsimp only [A]
    module
  have hm := trace_primitive_monotone hA hZ.1 hAZ
  have he : cfc (fun x : ℝ => (1 - q) * x - q) X = A := by
    rw [cfc_sub (fun x : ℝ => (1 - q) * x) (fun _ => q) X (by fun_prop) (by fun_prop),
      cfc_const_mul (1 - q) (fun x : ℝ => x) X (by fun_prop), cfc_id' ℝ X hX.1.isSelfAdjoint,
      cfc_const q X hX.1.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  have hf : Continuous PotentialScalar.primitive := continuous_iff_continuousAt.mpr
    (fun x => (PotentialScalar.primitive_derivative x).continuousAt)
  have hcomp : cfc (fun x : ℝ => PotentialScalar.primitive ((1 - q) * x - q)) X =
      cfc PotentialScalar.primitive A := by
    rw [← he]
    exact cfc_comp PotentialScalar.primitive (fun x : ℝ => (1 - q) * x - q) X
      hX.1.isSelfAdjoint hf.continuousOn (by fun_prop)
  have hb : (cfc PotentialScalar.primitive X).trace - (cfc PotentialScalar.primitive A).trace ≤
      8 * q * (cfc sizeWeight X).trace := by
    rw [← hcomp, trace_cfc hX.1, trace_cfc hX.1, trace_cfc hX.1,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact PotentialScalar.direct_scalar_bound (hX.eigenvalues_nonneg i) hq hq1
  rw [cfc_primitive_eq hX] at hb
  rw [cfc_primitive_eq hZ] at hm
  linarith

end EuclideanSteinitz.Spectral

namespace EuclideanSteinitz.Endpoint
open Matrix MatrixEnergy Spectral
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma diag_le {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (i : ι) : A i i ≤ B i i := by
  have h := (Matrix.le_iff.mp hAB).diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, sub_nonneg] using h

lemma diagonalize {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A * hA.eigenvectorUnitary =
      diagonal hA.eigenvalues := by
  conv_lhs => arg 1; arg 2; rw [real_spectral hA]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma inverse_spectral {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹ = (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) *
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) *
      (hA.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  rw [nonsing_inv_eq_ringInverse, ← cfc_ringInverse_id (R := ℝ) A hA.isUnit hA.1.isSelfAdjoint]
  exact real_cfc hA.1 _

lemma sandwich_diagonal_apply (M : Matrix ι ι ℝ) (w : ι → ℝ) (i : ι) :
    (M * diagonal w * M.transpose) i i = ∑ j, (M i j) ^ 2 * w j := by
  simp only [Matrix.mul_apply (M := M * diagonal w), mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma overlap_conjugate {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B * hA.eigenvectorUnitary =
      (overlapBasis hA hB : Matrix ι ι ℝ) * diagonal hB.eigenvalues *
        (overlapBasis hA hB : Matrix ι ι ℝ).transpose := by
  conv_lhs => rw [real_spectral hB]
  rw [overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

lemma overlap_row_weight {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hBA : B ≤ A) (i : ι) :
    ∑ j, (overlapBasis hA hB i j) ^ 2 * hB.eigenvalues j ≤ hA.eigenvalues i := by
  have h := Gain.congruence_mono hBA (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, diagonalize hA, overlap_conjugate hA hB] at h
  have hd := diag_le h i
  simpa only [sandwich_diagonal_apply, diagonal_apply_eq] using hd

lemma overlap_inverse_conjugate {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A⁻¹ * hB.eigenvectorUnitary =
      (overlapBasis hA.1 hB : Matrix ι ι ℝ).transpose *
        diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * overlapBasis hA.1 hB := by
  rw [inverse_spectral hA, overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

lemma diagonalize_inverse {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (hA.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A⁻¹ * hA.1.eigenvectorUnitary =
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) := by
  rw [inverse_spectral hA]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma overlap_col_inverse_weight {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (j : ι) :
    ∑ i, (overlapBasis hA.1 hB.1 i j) ^ 2 / hA.1.eigenvalues i ≤
      (hB.1.eigenvalues j)⁻¹ := by
  have h := Gain.congruence_mono (MatrixEnergy.inv_le_inv hB hA hBA)
    (hB.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, diagonalize_inverse hB,
    overlap_inverse_conjugate hA hB.1] at h
  have hd := diag_le h j
  have he := sandwich_diagonal_apply (overlapBasis hA.1 hB.1 : Matrix ι ι ℝ).transpose
    (fun i => (hA.1.eigenvalues i)⁻¹) j
  simp only [Matrix.transpose_transpose, transpose_apply] at he
  rw [he, diagonal_apply_eq] at hd
  simpa only [div_eq_mul_inv] using hd

lemma overlap_ratio_row {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (i : ι) :
    ∑ j, (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i ≤ 1 := by
  rw [← Finset.sum_div, div_le_one (hA.eigenvalues_pos i)]
  exact overlap_row_weight hA.1 hB.1 hBA i

lemma overlap_ratio_col {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (j : ι) :
    ∑ i, (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (overlap_col_inverse_weight hA hB hBA j)
    (hB.eigenvalues_pos j).le
  rw [inv_mul_cancel₀ (ne_of_gt (hB.eigenvalues_pos j)), Finset.sum_mul] at h
  calc
    _ = ∑ i, ((overlapBasis hA.1 hB.1 i j) ^ 2 / hA.1.eigenvalues i) *
        hB.1.eigenvalues j := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_right_comm _ _ _
    _ ≤ 1 := h

lemma trace_cfc_mul_diag {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (B : Matrix ι ι ℝ) (f : ℝ → ℝ) :
    (cfc f A * B).trace = ∑ i, f (hA.eigenvalues i) *
      ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B * hA.eigenvectorUnitary) i i := by
  rw [real_cfc hA f]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) *
        ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B *
          hA.eigenvectorUnitary)).trace := by
      simp only [Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.trace, Matrix.diag, diagonal_mul]

lemma gain_new_coordinates {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (cfc (fun x => cutoff x ^ 2) A * (A - B)).trace =
      ∑ i, hA.1.eigenvalues i *
        (1 - ∑ j, (overlapBasis hA.1 hB i j) ^ 2 * hB.eigenvalues j /
          hA.1.eigenvalues i) * cutoff (hA.1.eigenvalues i) ^ 2 := by
  rw [trace_cfc_mul_diag hA.1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, diagonalize hA.1,
    overlap_conjugate hA.1 hB, Matrix.sub_apply, diagonal_apply_eq,
    sandwich_diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_div]
  field_simp [ne_of_gt (hA.eigenvalues_pos i)]

lemma gain_endpoint {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) :
    ((cfc cutoff A - cfc cutoff B) * cfc (fun (x : ℝ) => 1 + x) B *
        (cfc cutoff A - cfc cutoff B).transpose).trace +
      (cfc (fun x => cutoff x ^ 2) A * (A - B)).trace ≤
      115200 * ((cfc potential A).trace - (cfc potential B).trace) := by
  rw [weighted_cfc_distance hA.1 hB.1, gain_new_coordinates hA hB.1,
    trace_cfc hA.1, trace_cfc hB.1]
  exact gain_spectral_bound hA.1.eigenvalues hB.1.eigenvalues
    (fun i j => (overlapBasis hA.1 hB.1 i j) ^ 2)
    (fun i j => (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i)
    hA.eigenvalues_pos hB.eigenvalues_pos (fun i j => sq_nonneg _)
    (sum_row_squares _) (sum_col_squares _) (fun _ _ => rfl)
    (overlap_ratio_row hA hB hBA) (overlap_ratio_col hA hB hBA)

end EuclideanSteinitz.Endpoint

namespace EuclideanSteinitz.Endpoint
open Matrix MatrixEnergy Spectral
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def transportBasis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * C * hB.eigenvectorUnitary

lemma transport_row_matrix {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) :
    transportBasis hA hB C * (transportBasis hA hB C).transpose =
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (C * C.transpose) *
        hA.eigenvectorUnitary := by
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_mul_transpose, Matrix.mul_one]

lemma transport_col_matrix {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) :
    (transportBasis hA hB C).transpose * transportBasis hA hB C =
      (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (C.transpose * C) *
        hB.eigenvectorUnitary := by
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_mul_transpose, Matrix.mul_one]

lemma transport_row_bound {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C * C.transpose ≤ 1) (i : ι) :
    ∑ j, transportBasis hA hB C i j ^ 2 ≤ 1 := by
  have h := Gain.congruence_mono hC (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, Matrix.mul_one, unitary_transpose_mul,
    ← transport_row_matrix hA hB C] at h
  have hd := diag_le h i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hd

lemma transport_col_bound {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C * C.transpose ≤ 1) (j : ι) :
    ∑ i, transportBasis hA hB C i j ^ 2 ≤ 1 := by
  have h := Gain.congruence_mono (transpose_contraction hC)
    (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, Matrix.mul_one, unitary_transpose_mul,
    ← transport_col_matrix hA hB C] at h
  have hd := diag_le h j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hd

lemma transport_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) :
    transportBasis hA hB C * diagonal hB.eigenvalues * (transportBasis hA hB C).transpose =
      diagonal hA.eigenvalues := by
  rw [← diagonalize hA]
  conv_rhs => arg 1; arg 2; rw [heq, real_spectral hB]
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma transport_row_weight {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) (i : ι) :
    ∑ j, transportBasis hA hB C i j ^ 2 * hB.eigenvalues j = hA.eigenvalues i := by
  have h := congr_fun (congr_fun (transport_spectral hA hB heq) i) i
  simpa only [sandwich_diagonal_apply, diagonal_apply_eq] using h

lemma congruence_inverse {A B C : Matrix ι ι ℝ}
    (hC : IsUnit C) (heq : A = C * B * C.transpose) :
    C.transpose * A⁻¹ * C = B⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det C).mp hC
  have ht := Matrix.isUnit_det_transpose C hd
  rw [heq, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

lemma transport_inverse_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) :
    (transportBasis hA.1 hB.1 C).transpose *
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * transportBasis hA.1 hB.1 C =
        diagonal (fun i => (hB.1.eigenvalues i)⁻¹) := by
  rw [← diagonalize_inverse hB, ← congruence_inverse hC heq, inverse_spectral hA]
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma transport_col_inverse_weight {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) (j : ι) :
    ∑ i, transportBasis hA.1 hB.1 C i j ^ 2 / hA.1.eigenvalues i =
      (hB.1.eigenvalues j)⁻¹ := by
  have h := congr_fun (congr_fun (transport_inverse_spectral hA hB hC heq) j) j
  have hh := sandwich_diagonal_apply (transportBasis hA.1 hB.1 C).transpose
    (fun i => (hA.1.eigenvalues i)⁻¹) j
  simp only [Matrix.transpose_transpose, Matrix.transpose_apply] at hh
  rw [hh, diagonal_apply_eq] at h
  simpa only [div_eq_mul_inv] using h

lemma transport_ratio_row {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) (i : ι) :
    ∑ j, transportBasis hA.1 hB C i j ^ 2 * hB.eigenvalues j / hA.1.eigenvalues i = 1 := by
  rw [← Finset.sum_div, transport_row_weight hA.1 hB heq,
    div_self (ne_of_gt (hA.eigenvalues_pos i))]

lemma transport_ratio_col {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) (j : ι) :
    ∑ i, transportBasis hA.1 hB.1 C i j ^ 2 * hB.1.eigenvalues j / hA.1.eigenvalues i = 1 := by
  calc
    _ = (∑ i, transportBasis hA.1 hB.1 C i j ^ 2 / hA.1.eigenvalues i) *
        hB.1.eigenvalues j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_right_comm _ _ _
    _ = 1 := by rw [transport_col_inverse_weight hA hB hC heq,
      inv_mul_cancel₀ (ne_of_gt (hB.eigenvalues_pos j))]

lemma trace_cfc_transport_product {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) (f g : ℝ → ℝ) :
    (cfc f A * C * cfc g B * C.transpose).trace = ∑ i, ∑ j,
      transportBasis hA hB C i j ^ 2 * f (hA.eigenvalues i) * g (hB.eigenvalues j) := by
  rw [real_cfc hA f, real_cfc hB g]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) * transportBasis hA hB C *
        diagonal (fun j => g (hB.eigenvalues j)) * (transportBasis hA hB C).transpose).trace := by
      simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [trace_diagonal_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

omit [DecidableEq ι] in
lemma contraction_distance_identity {κ : Type*} [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (m : ι → κ → ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hrow : ∀ i, ∑ j, m i j * y j = x i) :
    (∑ i, (1 + x i) * f i ^ 2) + (∑ j, (1 + y j) * g j ^ 2) -
      2 * (∑ i, ∑ j, m i j * (1 + y j) * f i * g j) =
    (∑ i, ∑ j, m i j * (1 + y j) * (f i - g j) ^ 2) +
      (∑ i, (1 - ∑ j, m i j) * f i ^ 2) +
      (∑ j, (1 - ∑ i, m i j) * (1 + y j) * g j ^ 2) := by
  have h1 : (∑ i, ∑ j, m i j * (1 + y j) * f i ^ 2) =
      (∑ i, (1 + x i) * f i ^ 2) - (∑ i, (1 - ∑ j, m i j) * f i ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hrow]
    ring
  have h2 : (∑ i, ∑ j, m i j * (1 + y j) * g j ^ 2) =
      (∑ j, (1 + y j) * g j ^ 2) -
        (∑ j, (1 - ∑ i, m i j) * (1 + y j) * g j ^ 2) := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hexpand (i : ι) (j : κ) : m i j * (1 + y j) * (f i - g j) ^ 2 =
      m i j * (1 + y j) * f i ^ 2 + m i j * (1 + y j) * g j ^ 2 -
        2 * (m i j * (1 + y j) * f i * g j) := by ring
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]
  ring

lemma contraction_endpoint_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (heq : A = C * B * C.transpose) :
    (cfc (fun x => (1 + x) * cutoff x ^ 2) A).trace +
      (cfc (fun x => (1 + x) * cutoff x ^ 2) B).trace -
      2 * (cfc cutoff A * C * cfc (fun x => (1 + x) * cutoff x) B * C.transpose).trace ≤
      115200 * ((cfc potential B).trace - (cfc potential A).trace) := by
  rw [trace_cfc hA.1, trace_cfc hB.1, trace_cfc_transport_product hA.1 hB.1,
    trace_cfc hA.1, trace_cfc hB.1]
  have hx : (∑ i, ∑ j, transportBasis hA.1 hB.1 C i j ^ 2 * cutoff (hA.1.eigenvalues i) *
      ((1 + hB.1.eigenvalues j) * cutoff (hB.1.eigenvalues j))) =
      ∑ i, ∑ j, transportBasis hA.1 hB.1 C i j ^ 2 * (1 + hB.1.eigenvalues j) *
        cutoff (hA.1.eigenvalues i) * cutoff (hB.1.eigenvalues j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx, contraction_distance_identity _ _ _ _ _ (transport_row_weight hA.1 hB.1 heq)]
  exact contraction_spectral_bound hA.1.eigenvalues hB.1.eigenvalues
    (fun i j => transportBasis hA.1 hB.1 C i j ^ 2)
    (fun i j => transportBasis hA.1 hB.1 C i j ^ 2 * hB.1.eigenvalues j / hA.1.eigenvalues i)
    hA.eigenvalues_pos hB.eigenvalues_pos (fun _ _ => sq_nonneg _)
    (transport_row_bound hA.1 hB.1 hContract) (transport_col_bound hA.1 hB.1 hContract)
    (fun _ _ => rfl) (transport_ratio_row hA hB.1 heq) (transport_ratio_col hA hB hC heq)

end EuclideanSteinitz.Endpoint

namespace EuclideanSteinitz.Coefficient
open Matrix MatrixEnergy Spectral Endpoint
open scoped MatrixOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def lift (R : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  R.transpose * A * R

noncomputable def weightedSq (D : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) : ℝ :=
  (D * W * D.transpose).trace

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_nonneg (D : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.PosSemidef) :
    0 ≤ weightedSq D W := by
  have h : (D * W * D.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.mul_mul_conjTranspose_same D
  exact h.trace_nonneg

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_weight_add (D : Matrix ι κ ℝ) (W V : Matrix κ κ ℝ) :
    weightedSq D (W + V) = weightedSq D W + weightedSq D V := by
  simp only [weightedSq, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weighted_cross_symm (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.transpose = W) :
    (D * W * E.transpose).trace = (E * W * D.transpose).trace := by
  rw [← Matrix.trace_transpose (D * W * E.transpose)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hW, Matrix.mul_assoc]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_sub (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.transpose = W) :
    weightedSq (D - E) W = weightedSq D W + weightedSq E W -
      2 * (D * W * E.transpose).trace := by
  simp only [weightedSq, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [weighted_cross_symm E D hW]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_triangle (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.PosSemidef) :
    weightedSq (D + E) W ≤ 2 * weightedSq D W + 2 * weightedSq E W := by
  have hn := weightedSq_nonneg (D - E) hW
  have hi : weightedSq (D + E) W + weightedSq (D - E) W =
      2 * weightedSq D W + 2 * weightedSq E W := by
    simp only [weightedSq, Matrix.transpose_add, Matrix.transpose_sub, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  linarith only [hn, hi]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma lift_transpose (R : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) :
    (lift R A).transpose = lift R A.transpose := by
  simp only [lift, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma lift_sub (R : Matrix ι κ ℝ) (A B : Matrix ι ι ℝ) :
    lift R (A - B) = lift R A - lift R B := by
  simp only [lift, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weighted_lift_cross (R S : Matrix ι κ ℝ) (A B : Matrix ι ι ℝ)
    (W : Matrix κ κ ℝ) :
    (lift R A * W * (lift S B).transpose).trace =
      (A * (R * W * S.transpose) * B.transpose * (S * R.transpose)).trace := by
  simp only [lift, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm R.transpose]
  simp only [Matrix.mul_assoc]

omit [DecidableEq κ] in
lemma weighted_lift (R : Matrix ι κ ℝ) (hR : R * R.transpose = 1)
    (A : Matrix ι ι ℝ) (W : Matrix κ κ ℝ) :
    weightedSq (lift R A) W = weightedSq A (R * W * R.transpose) := by
  unfold weightedSq
  rw [weighted_lift_cross, hR, Matrix.mul_one]

lemma cfc_transpose {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).transpose = cfc f A := by
  rw [real_cfc hA f]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma cfc_square {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A * cfc f A = cfc (fun x => f x ^ 2) A := by
  rw [real_cfc hA f, real_cfc hA (fun x => f x ^ 2)]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.diagonal_mul_diagonal]
  simp only [sq]

lemma cfc_affine {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => 1 + x) A = 1 + A := by
  rw [cfc_add A (fun _ : ℝ => 1) (fun x : ℝ => x) continuousOn_const continuousOn_id,
    cfc_const_one ℝ A, cfc_id' ℝ A hA.isSelfAdjoint]

lemma weightedSq_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (W : Matrix ι ι ℝ) :
    weightedSq (cfc f A) W = (cfc (fun x => f x ^ 2) A * W).trace := by
  unfold weightedSq
  rw [cfc_transpose hA f, Matrix.trace_mul_cycle, cfc_square hA]

lemma cfc_mul_same {A : Matrix ι ι ℝ} (_hA : A.IsHermitian) (f g : ℝ → ℝ) :
    cfc f A * cfc g A = cfc (fun x => f x * g x) A := by
  have hf : ContinuousOn f (spectrum ℝ A) := Gain.finite_spectrum_continuous _ _
  have hg : ContinuousOn g (spectrum ℝ A) := Gain.finite_spectrum_continuous _ _
  exact (cfc_mul f g A hf hg).symm

lemma weightedSq_cfc_affine {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    weightedSq (cfc f A) (1 + A) = (cfc (fun x => (1 + x) * f x ^ 2) A).trace := by
  rw [weightedSq_cfc hA, ← cfc_affine hA, cfc_mul_same hA]
  congr 2
  funext x
  exact mul_comm _ _

omit [DecidableEq κ] in
lemma contraction_endpoint {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (heq : A = C * B * C.transpose)
    (R S : Matrix ι κ ℝ) (hR : R * R.transpose = 1) (hS : S * S.transpose = 1)
    (W : Matrix κ κ ℝ) (hW : W.transpose = W)
    (hRW : R * W * R.transpose = 1 + A) (hSW : S * W * S.transpose = 1 + B)
    (hRS : R * S.transpose = C) (hRWS : R * W * S.transpose = C * (1 + B)) :
    weightedSq (lift R (cfc cutoff A) - lift S (cfc cutoff B)) W ≤
      115200 * ((cfc potential B).trace - (cfc potential A).trace) := by
  have hSR : S * R.transpose = C.transpose := by
    rw [← hRS, Matrix.transpose_mul, Matrix.transpose_transpose]
  have haff : (1 + B) * cfc cutoff B = cfc (fun x => (1 + x) * cutoff x) B := by
    rw [← cfc_affine hB.1, cfc_mul_same hB.1]
  have hcross : (lift R (cfc cutoff A) * W * (lift S (cfc cutoff B)).transpose).trace =
      (cfc cutoff A * C * cfc (fun x => (1 + x) * cutoff x) B * C.transpose).trace := by
    rw [weighted_lift_cross, hRWS, cfc_transpose hB.1, hSR, ← haff]
    simp only [Matrix.mul_assoc]
  rw [weightedSq_sub _ _ hW, weighted_lift R hR, weighted_lift S hS, hRW, hSW,
    weightedSq_cfc_affine hA.1, weightedSq_cfc_affine hB.1, hcross]
  exact contraction_endpoint_spectral hA hB hC hContract heq

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_sub_zero (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ}
    (hW : W.transpose = W) (hEW : E * W = 0) :
    weightedSq (D - E) W = weightedSq D W := by
  rw [weightedSq_sub _ _ hW, weighted_cross_symm D E hW]
  simp only [weightedSq, hEW, Matrix.zero_mul, Matrix.trace_zero, mul_zero, add_zero, sub_zero]

lemma gain_endpoint_lift {X Z : Matrix ι ι ℝ}
    (hX : X.PosDef) (hZ : Z.PosDef) (hZX : Z ≤ X)
    (R : Matrix ι κ ℝ) (hR : R * R.transpose = 1)
    (E Qold Qnew : Matrix κ κ ℝ) (hNew : Qnew.transpose = Qnew)
    (hEq : E * Qnew = 0)
    (hOld : R * Qold * R.transpose = Z) (hNewState : R * Qnew * R.transpose = X - Z) :
    weightedSq (lift R (cfc cutoff X) - lift R (cfc cutoff Z)) (1 + Qold) +
      weightedSq (lift R (cfc cutoff X) - E) Qnew ≤
      115200 * ((cfc potential X).trace - (cfc potential Z).trace) := by
  rw [← lift_sub, weighted_lift R hR,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hR, hOld,
    weightedSq_sub_zero _ _ hNew hEq, weighted_lift R hR, hNewState,
    weightedSq_cfc hX.1, ← cfc_affine hZ.1]
  exact gain_endpoint hX hZ hZX

lemma endpoint_comparison {X Y Z C : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (hZeq : Z = C * Y * C.transpose)
    (T S : Matrix ι κ ℝ) (hT : T * T.transpose = 1) (hS : S * S.transpose = 1)
    (Qold Qnew : Matrix κ κ ℝ) (hOldPSD : Qold.PosSemidef) (hNewPSD : Qnew.PosSemidef)
    (hOldS : S * Qold * S.transpose = Y) (hOldT : T * Qold * T.transpose = Z)
    (hTS : T * S.transpose = C) (hCross : T * Qold * S.transpose = C * Y)
    (hNewT : T * Qnew * T.transpose = X - Z)
    (hZero : lift S (cfc cutoff Y) * Qnew = 0) :
    weightedSq (lift T (cfc cutoff X) - lift S (cfc cutoff Y)) ((1 + Qold) + Qnew) ≤
      230400 * (((cfc potential Y).trace - (cfc potential Z).trace) +
        ((cfc potential X).trace - (cfc potential Z).trace)) := by
  let F1 := lift T (cfc cutoff X)
  let Fm := lift T (cfc cutoff Z)
  let F0 := lift S (cfc cutoff Y)
  let W := (1 : Matrix κ κ ℝ) + Qold
  have hWPSD : W.PosSemidef := Matrix.PosSemidef.one.add hOldPSD
  have hWsymm : W.transpose = W := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hWPSD.1
  have hNewSymm : Qnew.transpose = Qnew := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hNewPSD.1
  have hTW : T * W * T.transpose = 1 + Z := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hT, hOldT]
  have hSW : S * W * S.transpose = 1 + Y := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS, hOldS]
  have hTWS : T * W * S.transpose = C * (1 + Y) := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS, hCross]
  have hZX : Z ≤ X := by
    apply Matrix.le_iff.mpr
    rw [← hNewT]
    simpa only [conjTranspose_eq_transpose_of_trivial] using hNewPSD.mul_mul_conjTranspose_same T
  have hcontr := contraction_endpoint hZ hY hC hContract hZeq T S hT hS W hWsymm
    hTW hSW hTS hTWS
  change weightedSq (Fm - F0) W ≤ _ at hcontr
  have hgain := gain_endpoint_lift hX hZ hZX T hT F0 Qold Qnew hNewSymm hZero hOldT hNewT
  change weightedSq (F1 - Fm) W + weightedSq (F1 - F0) Qnew ≤ _ at hgain
  have hpos := weightedSq_nonneg (F1 - F0) hNewPSD
  have htri : weightedSq (F1 - F0) W ≤
      2 * weightedSq (F1 - Fm) W + 2 * weightedSq (Fm - F0) W := by
    have heq : F1 - F0 = (F1 - Fm) + (Fm - F0) := by abel
    conv_lhs => rw [heq]
    exact weightedSq_triangle _ _ hWPSD
  change weightedSq (F1 - F0) (W + Qnew) ≤ _
  rw [weightedSq_weight_add]
  linarith only [htri, hgain, hcontr, hpos]

end EuclideanSteinitz.Coefficient

end OAI
