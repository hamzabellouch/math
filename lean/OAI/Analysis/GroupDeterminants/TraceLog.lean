import OAI.Analysis.GroupDeterminants.LogSeries

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section TraceCFC
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

lemma hasDerivAt_trace_log_one_sub (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {f f' : ℝ → A} {x : ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hc : ContinuousAt f' x) (hn : ‖f x‖ < 1) (hself : ∀ y, IsSelfAdjoint (f y)) :
    HasDerivAt (fun y => τ (CFC.log (1 - f y)))
      (-τ (f' x * Ring.inverse (1 - f x))) x := by
  have hd := (hasDerivAt_trace_logSeries_local τ hτ hf hc hn).neg
  apply hd.congr_of_eventuallyEq
  have he : ∀ᶠ y in 𝓝 x, ‖f y‖ < 1 :=
    (hf x).continuousAt.norm.eventually (gt_mem_nhds hn)
  filter_upwards [he] with y hy
  have hh := (τ.hasSum (hasSum_pow_div_cfc_log (f y) (hself y) hy)).tsum_eq
  simpa only [map_neg, neg_neg, Pi.neg_apply] using (congrArg Neg.neg hh).symm

omit [Nontrivial A] in
lemma log_smul_of_isUnit (V : A) (hV : IsSelfAdjoint V) (hu : IsUnit V)
    (c : ℝ) (hc : 0 < c) :
    CFC.log (c • V) = Real.log c • (1 : A) + CFC.log V := by
  have hne (x : ℝ) (hx : x ∈ spectrum ℝ V) : x ≠ 0 := by
    intro he
    exact (spectrum.zero_notMem_iff ℝ).mpr hu (he ▸ hx)
  have hl : ContinuousOn Real.log (spectrum ℝ V) := by
    intro x hx
    exact (Real.continuousAt_log (hne x hx)).continuousWithinAt
  have hlc : ContinuousOn Real.log ((fun x : ℝ => c * x) '' spectrum ℝ V) := by
    rintro y ⟨x, hx, rfl⟩
    exact (Real.continuousAt_log (mul_ne_zero hc.ne' (hne x hx))).continuousWithinAt
  have he : cfc (fun x : ℝ => c * x) V = c • V := cfc_const_mul_id c V hV
  rw [CFC.log, ← he, ← cfc_comp' Real.log (fun x : ℝ => c * x) V hlc (by fun_prop) hV]
  calc
    cfc (fun x : ℝ => Real.log (c * x)) V =
        cfc (fun x : ℝ => Real.log c + Real.log x) V := by
      apply cfc_congr
      intro x hx
      exact Real.log_mul hc.ne' (hne x hx)
    _ = Real.log c • (1 : A) + CFC.log V := by
      rw [cfc_add V (fun _ : ℝ => Real.log c) Real.log (by fun_prop) hl,
        cfc_const (Real.log c) V hV, Algebra.algebraMap_eq_smul_one]
      rfl

lemma norm_one_sub_rescale_star_mul_self (M : A) (hu : IsUnit M) :
    ‖1 - (‖star M * M‖ + 1)⁻¹ • (star M * M)‖ < 1 := by
  let N := star M * M
  let c := ‖N‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : IsSelfAdjoint N := IsSelfAdjoint.star_mul_self M
  have huN : IsUnit N := hu.star.mul hu
  have he : cfc (fun x : ℝ => 1 - c⁻¹ * x) N = 1 - c⁻¹ • N := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x => c⁻¹ * x) N (by fun_prop) (by fun_prop),
      cfc_const_one ℝ N hN, cfc_const_mul_id c⁻¹ N hN]
  change ‖1 - c⁻¹ • N‖ < 1
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro x hx
  have hx₀ : 0 < x := by
    have hn : 0 ≤ x := spectrum_star_mul_self_nonneg x hx
    have hnz : x ≠ 0 := fun hz => (spectrum.zero_notMem_iff ℝ).mpr huN (hz ▸ hx)
    exact lt_of_le_of_ne hn (Ne.symm hnz)
  have hxn : x < c := by
    have hb := spectrum.norm_le_norm_of_mem hx
    dsimp [c]
    rw [Real.norm_of_nonneg hx₀.le] at hb
    linarith
  rw [Real.norm_eq_abs, abs_lt]
  have hxc : 0 < c⁻¹ * x := mul_pos (inv_pos.mpr hc) hx₀
  have hxc' : c⁻¹ * x < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hc).mpr hxn
  constructor <;> linarith

omit [Nontrivial A] in
lemma ringInverse_smul (N : A) (hu : IsUnit N) (c : ℝ) (hc : c ≠ 0) :
    Ring.inverse (c • N) = c⁻¹ • Ring.inverse N := by
  have hu' : IsUnit (c • N) := by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)).mul hu
  have hm : (c • N) * (c⁻¹ • Ring.inverse N) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Ring.mul_inverse_cancel N hu]
  calc
    Ring.inverse (c • N) = Ring.inverse (c • N) * 1 := (mul_one _).symm
    _ = Ring.inverse (c • N) * ((c • N) * (c⁻¹ • Ring.inverse N)) := by rw [hm]
    _ = c⁻¹ • Ring.inverse N := Ring.inverse_mul_cancel_left _ _ hu'

lemma hasDerivAt_trace_log_of_rescale (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {N N' : ℝ → A} {x c : ℝ} (hc : 0 < c)
    (hd : ∀ y, HasDerivAt N (N' y) y) (hdc : ContinuousAt N' x)
    (hself : ∀ y, IsSelfAdjoint (N y)) (hu : ∀ y, IsUnit (N y))
    (hn : ‖1 - c⁻¹ • N x‖ < 1) :
    HasDerivAt (fun y => τ (CFC.log (N y)))
      (τ (N' x * Ring.inverse (N x))) x := by
  let W := fun y => (1 : A) - c⁻¹ • N y
  let W' := fun y => -(c⁻¹ • N' y)
  have hW (y : ℝ) : HasDerivAt W (W' y) y := by
    simpa [W, W'] using (hd y).const_smul c⁻¹ |>.const_sub 1
  have hWc : ContinuousAt W' x := (hdc.const_smul c⁻¹).neg
  have hWs (y : ℝ) : IsSelfAdjoint (W y) :=
    (IsSelfAdjoint.one A).sub ((IsSelfAdjoint.all (c⁻¹)).smul (hself y))
  have he (y : ℝ) : 1 - W y = c⁻¹ • N y := by dsimp [W]; abel
  have hue (y : ℝ) : IsUnit (1 - W y) := by
    rw [he, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hc.ne')).map (algebraMap ℝ A)).mul (hu y)
  have hrescale (y : ℝ) : c • (1 - W y) = N y := by
    rw [he, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hlog (y : ℝ) : CFC.log (N y) = Real.log c • (1 : A) + CFC.log (1 - W y) := by
    rw [← hrescale y]
    exact log_smul_of_isUnit (1 - W y) ((IsSelfAdjoint.one A).sub (hWs y)) (hue y) c hc
  have H := (hasDerivAt_trace_log_one_sub τ hτ hW hWc hn hWs).const_add
    (τ (Real.log c • (1 : A)))
  have hdval : -τ (W' x * Ring.inverse (1 - W x)) = τ (N' x * Ring.inverse (N x)) := by
    rw [he, ringInverse_smul (N x) (hu x) _ (inv_ne_zero hc.ne'), inv_inv]
    dsimp [W']
    rw [neg_mul, smul_mul_smul_comm, inv_mul_cancel₀ hc.ne', one_smul, map_neg, neg_neg]
  rw [hdval] at H
  convert! H using 1
  ext y
  rw [hlog, map_add]

omit [Nontrivial A] in
lemma trace_star_mul_self_log_derivative_value (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (M D : A) (hu : IsUnit M) :
    τ ((star D * M + star M * D) * Ring.inverse (star M * M)) =
      (2 * (τ (D * Ring.inverse M)).re : ℝ) := by
  rw [add_mul, map_add]
  have hfirst : τ (star D * M * Ring.inverse (star M * M)) =
      star (τ (D * Ring.inverse M)) := by
    rw [Ring.inverse_mul (Or.inl hu.star), ← mul_assoc,
      Ring.mul_inverse_cancel_right M (star D) hu, hτ, Ring.inverse_star,
      ← star_mul, hstar]
  have hsecond : τ (star M * D * Ring.inverse (star M * M)) = τ (D * Ring.inverse M) := by
    rw [mul_assoc, hτ, Ring.inverse_mul (Or.inl hu.star), mul_assoc D,
      mul_assoc (Ring.inverse M), Ring.inverse_mul_cancel (star M) hu.star, mul_one]
  rw [hfirst, hsecond, add_comm]
  exact Complex.add_conj _

lemma hasDerivAt_trace_log_star_mul_self (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    {M M' : ℝ → A} {x : ℝ} (hd : ∀ y, HasDerivAt M (M' y) y)
    (hdc : ContinuousAt M' x) (hu : ∀ y, IsUnit (M y)) :
    HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)))
      (2 * (τ (M' x * Ring.inverse (M x))).re : ℝ) x := by
  let N := fun y => star (M y) * M y
  let N' := fun y => star (M' y) * M y + star (M y) * M' y
  have hN (y : ℝ) : HasDerivAt N (N' y) y := (hd y).star.mul (hd y)
  have hNc : ContinuousAt N' x :=
    (hdc.star.mul (hd x).continuousAt).add ((hd x).continuousAt.star.mul hdc)
  have H := hasDerivAt_trace_log_of_rescale τ hτ
    (show 0 < ‖N x‖ + 1 by positivity) hN hNc
    (fun y => IsSelfAdjoint.star_mul_self (M y)) (fun y => (hu y).star.mul (hu y))
    (norm_one_sub_rescale_star_mul_self (M x) (hu x))
  rwa [trace_star_mul_self_log_derivative_value τ hτ hstar (M x) (M' x) (hu x)] at H

omit [Nontrivial A] in
lemma trace_derivative_mul_value (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (L R D E : A)
    (hL : IsUnit L) (hR : IsUnit R) :
    τ ((D * R + L * E) * Ring.inverse (L * R)) =
      τ (D * Ring.inverse L) + τ (E * Ring.inverse R) := by
  rw [add_mul, map_add, Ring.inverse_mul (Or.inl hL)]
  congr 1
  · rw [← mul_assoc, Ring.mul_inverse_cancel_right R D hR]
  · rw [mul_assoc L, hτ L, ← mul_assoc E, mul_assoc (E * Ring.inverse R),
      Ring.inverse_mul_cancel L hL, mul_one]

omit [Nontrivial A] in
def nilpotentShearUnit (S : A) (hS : S * S = 0) (x : ℝ) : Aˣ where
  val := 1 + x • S
  inv := 1 - x • S
  val_inv := by
    simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, hS, smul_zero]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hS, smul_zero]
    abel

omit [Nontrivial A] in
lemma ringInverse_nilpotentShear (S : A) (hS : S * S = 0) (x : ℝ) :
    Ring.inverse (1 + x • S) = 1 - x • S :=
  Ring.inverse_unit (nilpotentShearUnit S hS x)

omit [Nontrivial A] in
lemma nilpotentShear_trace_derivative (τ : A →L[ℝ] ℂ) (S : A)
    (hS : S * S = 0) (ht : τ S = 0) (x : ℝ) :
    τ (S * Ring.inverse (1 + x • S)) = 0 := by
  rw [ringInverse_nilpotentShear S hS x, mul_sub, mul_one, mul_smul_comm, hS,
    smul_zero, sub_zero, ht]

lemma trace_log_shear_invariant (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (B S T : A) (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : τ S = 0) (htT : τ T = 0) (x : ℝ) :
    τ (CFC.log (star ((1 + x • S) * B * (1 + x • T)) *
      ((1 + x • S) * B * (1 + x • T)))) = τ (CFC.log (star B * B)) := by
  let M := fun y : ℝ => (1 + y • S) * B * (1 + y • T)
  let M' := fun y : ℝ => S * B * (1 + y • T) + (1 + y • S) * B * T
  have hL (y : ℝ) : HasDerivAt (fun y : ℝ => 1 + y • S) S y := by
    simpa using ((hasDerivAt_id y).smul_const S).const_add 1
  have hR (y : ℝ) : HasDerivAt (fun y : ℝ => 1 + y • T) T y := by
    simpa using ((hasDerivAt_id y).smul_const T).const_add 1
  have hd (y : ℝ) : HasDerivAt M (M' y) y := ((hL y).mul_const B).mul (hR y)
  have hdc : Continuous M' := by dsimp [M']; fun_prop
  have huL (y : ℝ) : IsUnit (1 + y • S) := (nilpotentShearUnit S hS y).isUnit
  have huR (y : ℝ) : IsUnit (1 + y • T) := (nilpotentShearUnit T hT y).isUnit
  have hu (y : ℝ) : IsUnit (M y) := ((huL y).mul hB).mul (huR y)
  have hz (y : ℝ) : τ (M' y * Ring.inverse (M y)) = 0 := by
    dsimp [M, M']
    rw [trace_derivative_mul_value τ hτ _ _ _ _ ((huL y).mul hB) (huR y),
      Ring.inverse_mul (Or.inl (huL y)), ← mul_assoc,
      Ring.mul_inverse_cancel_right B S hB,
      nilpotentShear_trace_derivative τ S hS htS,
      nilpotentShear_trace_derivative τ T hT htT, add_zero]
  have H (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y))) 0 y := by
    simpa only [hz y, Complex.zero_re, mul_zero, Complex.ofReal_zero] using
      hasDerivAt_trace_log_star_mul_self τ hτ hstar hd hdc.continuousAt hu (x := y)
  have he := is_const_of_deriv_eq_zero (fun y => (H y).differentiableAt)
    (fun y => (H y).deriv) x 0
  simpa [M] using he

end TraceCFC

end GroupRingDeterminant

end

end OAI
