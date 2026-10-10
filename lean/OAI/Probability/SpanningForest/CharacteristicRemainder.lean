import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem336.Innovation

theorem norm_exp_mul_I_remainder_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  let z : ℂ := (x : ℂ) * Complex.I
  have hz : ‖z‖ = |x| := by simp [z]
  have hpoly : (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
      1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, z, mul_pow, Complex.I_sq]
    ring
  by_cases hx : |x| ≤ 1
  · have h := Complex.exp_bound (x := z) (by simpa [hz] using hx) (n := 3) (by decide)
    rw [hz, hpoly] at h
    have heq : Complex.exp z - (1 + (x : ℂ) * Complex.I - (x : ℂ)^2 / 2) =
        Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ)^2 / 2 := by dsimp [z]; ring
    rw [heq] at h
    norm_num at h
    exact h.trans (by nlinarith [pow_nonneg (abs_nonneg x) 3])
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have habs : 0 ≤ |x| := abs_nonneg x
    have hexp : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by simp
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ)^2 / 2‖
        ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
          ‖(x : ℂ) * Complex.I‖ + ‖(x : ℂ)^2 / 2‖ := by
            calc
              _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
                  ‖(x : ℂ)^2 / 2‖ := norm_add_le _ _
              _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
                  ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ)^2 / 2‖ := by
                    gcongr
                    exact norm_sub_le _ _
              _ ≤ _ := by
                gcongr
                exact norm_sub_le _ _
      _ = 2 + |x| + |x|^2 / 2 := by norm_num [hexp]
      _ ≤ 4 * |x|^3 := by
        have hsq : |x| ≤ |x|^2 := by nlinarith
        have hcube : |x|^2 ≤ |x|^3 := by nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx1)]
        nlinarith

theorem norm_integral_exp_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ) :
    ‖(∫ ω, Complex.exp ((X ω : ℂ) * Complex.I) ∂μ) -
        (μ.real Set.univ : ℂ) - (∫ ω, X ω ∂μ : ℝ) * Complex.I +
        (∫ ω, X ω ^ 2 ∂μ : ℝ) / 2‖ ≤
      4 * ∫ ω, |X ω| ^ 3 ∂μ := by
  have hcX : Integrable (fun ω => (X ω : ℂ)) μ := hX.ofReal
  have hcX2 : Integrable (fun ω => (((X ω) ^ 2 : ℝ) : ℂ)) μ := hX2.ofReal
  have hE : Integrable (fun ω => Complex.exp ((X ω : ℂ) * Complex.I)) μ := by
    apply Integrable.of_bound
      (Complex.continuous_exp.comp_aestronglyMeasurable
        (hcX.aestronglyMeasurable.mul_const Complex.I)) 1
    filter_upwards [] with ω
    simp
  have hcX2' : Integrable (fun ω => (X ω : ℂ) ^ 2 / 2) μ := by
    simpa using hcX2.div_const 2
  have hE1 : Integrable (fun ω => Complex.exp ((X ω : ℂ) * Complex.I) - 1) μ :=
    hE.sub (integrable_const 1)
  have hS : Integrable (fun ω => Complex.exp ((X ω : ℂ) * Complex.I) - 1 -
      (X ω : ℂ) * Complex.I) μ := hE1.sub (hcX.mul_const Complex.I)
  have hR : Integrable (fun ω => Complex.exp ((X ω : ℂ) * Complex.I) - 1 -
      (X ω : ℂ) * Complex.I + (X ω : ℂ) ^ 2 / 2) μ :=
    ((hE.sub (integrable_const 1)).sub (hcX.mul_const Complex.I)).add hcX2'
  have hrew : (∫ ω, Complex.exp ((X ω : ℂ) * Complex.I) - 1 -
      (X ω : ℂ) * Complex.I + (X ω : ℂ) ^ 2 / 2 ∂μ) =
      (∫ ω, Complex.exp ((X ω : ℂ) * Complex.I) ∂μ) -
        (μ.real Set.univ : ℂ) - (∫ ω, X ω ∂μ : ℝ) * Complex.I +
        (∫ ω, X ω ^ 2 ∂μ : ℝ) / 2 := by
    rw [integral_add hS hcX2', integral_sub hE1 (hcX.mul_const Complex.I),
      integral_sub hE (integrable_const 1)]
    simp only [integral_const, integral_mul_const, integral_div,
      ← Complex.ofReal_pow, integral_complex_ofReal, Complex.real_smul, mul_one]
  rw [← hrew]
  calc
    _ ≤ ∫ ω, ‖Complex.exp ((X ω : ℂ) * Complex.I) - 1 -
        (X ω : ℂ) * Complex.I + (X ω : ℂ) ^ 2 / 2‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 4 * |X ω| ^ 3 ∂μ :=
      integral_mono hR.norm (hX3.const_mul 4) (fun ω => norm_exp_mul_I_remainder_le (X ω))
    _ = _ := integral_const_mul _ _

theorem norm_condExp_exp_remainder_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun ω => Complex.exp ((X ω : ℂ) * Complex.I) | m] ω - 1 -
        (μ[X | m] ω : ℂ) * Complex.I +
        (μ[fun ω => X ω ^ 2 | m] ω : ℂ) / 2‖ ≤
      4 * μ[fun ω => |X ω| ^ 3 | m] ω := by
  let E : Ω → ℂ := fun ω => Complex.exp ((X ω : ℂ) * Complex.I)
  let S : Ω → ℂ := fun ω => E ω - 1 - (X ω : ℂ) * Complex.I
  let R : Ω → ℂ := fun ω => S ω + (X ω : ℂ) ^ 2 / 2
  have hcX : Integrable (fun ω => (X ω : ℂ)) μ := hX.ofReal
  have hcX2 : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) μ := hX2.ofReal
  have hE : Integrable E μ := by
    apply Integrable.of_bound
      (Complex.continuous_exp.comp_aestronglyMeasurable
        (hcX.aestronglyMeasurable.mul_const Complex.I)) 1
    filter_upwards [] with ω
    simp
  have hE1 : Integrable (fun ω => E ω - 1) μ := hE.sub (integrable_const 1)
  have hS : Integrable S μ := hE1.sub (hcX.mul_const Complex.I)
  have hQ : Integrable (fun ω => (X ω : ℂ) ^ 2 / 2) μ := by
    simpa only [Complex.ofReal_pow] using hcX2.div_const 2
  have hR : Integrable R μ := hS.add hQ
  have hnorm : ∀ᵐ ω ∂μ, ‖μ[R | m] ω‖ ≤ 4 * μ[fun ω => |X ω| ^ 3 | m] ω := by
    have hmono := condExp_mono (m := m) hR.norm (hX3.const_mul 4)
      (Filter.Eventually.of_forall (fun ω => norm_exp_mul_I_remainder_le (X ω)))
    have hscale := condExp_smul (μ := μ) (4 : ℝ) (fun ω => |X ω| ^ 3) m
    filter_upwards [norm_condExp_le (m := m) R, hmono, hscale] with ω h₁ h₂ h₃
    exact h₁.trans (h₂.trans_eq h₃)
  have hcx : (fun ω => (μ[X | m] ω : ℂ)) =ᵐ[μ] μ[fun ω => (X ω : ℂ) | m] := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.comp_condExp_comm (m := m) hX)
  have hcx2 : (fun ω => (μ[fun ω => X ω ^ 2 | m] ω : ℂ)) =ᵐ[μ]
      μ[fun ω => (X ω : ℂ) ^ 2 | m] := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_pow] using
      (Complex.ofRealCLM.comp_condExp_comm (m := m) hX2)
  have hmul : μ[fun ω => (X ω : ℂ) * Complex.I | m] =ᵐ[μ]
      (fun ω => μ[fun ω => (X ω : ℂ) | m] ω * Complex.I) := by
    have h := condExp_smul (μ := μ) Complex.I (fun ω => (X ω : ℂ)) m
    change μ[fun ω => Complex.I * (X ω : ℂ) | m] =ᵐ[μ]
      (fun ω => Complex.I * μ[fun ω => (X ω : ℂ) | m] ω) at h
    simpa only [mul_comm] using h
  have hdiv : μ[fun ω => (X ω : ℂ) ^ 2 / 2 | m] =ᵐ[μ]
      (fun ω => μ[fun ω => (X ω : ℂ) ^ 2 | m] ω / 2) := by
    have h := condExp_smul (μ := μ) ((2 : ℂ)⁻¹) (fun ω => (X ω : ℂ)^2) m
    change μ[fun ω => (2 : ℂ)⁻¹ * (X ω : ℂ)^2 | m] =ᵐ[μ]
      (fun ω => (2 : ℂ)⁻¹ * μ[fun ω => (X ω : ℂ)^2 | m] ω) at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  filter_upwards [hnorm, condExp_add hS hQ m,
    condExp_sub hE1 (hcX.mul_const Complex.I) m,
    condExp_sub hE (integrable_const (1 : ℂ)) m,
    hcx, hcx2, hmul, hdiv] with ω hn ha hs he hx hx2 hmulω hdivω
  change μ[R | m] ω = μ[S | m] ω + μ[fun ω => (X ω : ℂ)^2 / 2 | m] ω at ha
  change μ[S | m] ω = μ[fun ω => E ω - 1 | m] ω -
    μ[fun ω => (X ω : ℂ) * Complex.I | m] ω at hs
  change μ[fun ω => E ω - 1 | m] ω = μ[E | m] ω - μ[fun _ => (1 : ℂ) | m] ω at he
  change ‖μ[R | m] ω‖ ≤ _ at hn
  rw [ha, hs, he, condExp_const hm, hmulω, hdivω, ← hx, ← hx2] at hn
  exact hn

theorem norm_sub_gaussian_char_le
    {z : ℂ} {m₂ v ε δ : ℝ} (hv : 0 ≤ v) (hv₂ : v ≤ 2)
    (hz : ‖z - 1 + (m₂ : ℂ) / 2‖ ≤ ε) (hm₂ : |m₂ - v| ≤ δ) :
    ‖z - Complex.exp (-(v : ℂ) / 2)‖ ≤ ε + δ / 2 + v ^ 2 / 4 := by
  have hsmall : ‖-(v : ℂ) / 2‖ ≤ 1 := by
    norm_num [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    linarith
  have hexp : ‖(1 : ℂ) - (v : ℂ) / 2 - Complex.exp (-(v : ℂ) / 2)‖ ≤ v ^ 2 / 4 := by
    have h := Complex.norm_exp_sub_one_sub_id_le hsmall
    have heq : (1 : ℂ) - (v : ℂ) / 2 - Complex.exp (-(v : ℂ) / 2) =
      -(Complex.exp (-(v : ℂ) / 2) - 1 - (-(v : ℂ) / 2)) := by ring
    rw [heq, norm_neg]
    convert h using 1
    norm_num [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    ring
  have hdiff : ‖((v - m₂ : ℝ) : ℂ) / 2‖ ≤ δ / 2 := by
    have heq : ‖((v - m₂ : ℝ) : ℂ) / 2‖ = |v - m₂| / 2 := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [heq, abs_sub_comm]
    exact div_le_div_of_nonneg_right hm₂ (by norm_num)
  have heq : z - Complex.exp (-(v : ℂ) / 2) =
      (z - 1 + (m₂ : ℂ) / 2) + ((v - m₂ : ℝ) : ℂ) / 2 +
      ((1 : ℂ) - (v : ℂ) / 2 - Complex.exp (-(v : ℂ) / 2)) := by
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖z - 1 + (m₂ : ℂ) / 2 + ((v - m₂ : ℝ) : ℂ) / 2‖ +
        ‖(1 : ℂ) - (v : ℂ) / 2 - Complex.exp (-(v : ℂ) / 2)‖ := norm_add_le _ _
    _ ≤ (‖z - 1 + (m₂ : ℂ) / 2‖ + ‖((v - m₂ : ℝ) : ℂ) / 2‖) +
        ‖(1 : ℂ) - (v : ℂ) / 2 - Complex.exp (-(v : ℂ) / 2)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hz hdiff) hexp

theorem conditional_characteristic_error
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) μ)
    {v δ η : ℝ} (hv : 0 ≤ v) (hv₂ : v ≤ 2)
    (hmean : μ[X | m] =ᵐ[μ] 0)
    (hsecond : ∀ᵐ ω ∂μ, |μ[fun ω => X ω ^ 2 | m] ω - v| ≤ δ)
    (hthird : ∀ᵐ ω ∂μ, μ[fun ω => |X ω| ^ 3 | m] ω ≤ η) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun ω => Complex.exp ((X ω : ℂ) * Complex.I) | m] ω -
        Complex.exp (-(v : ℂ) / 2)‖ ≤ 4 * η + δ / 2 + v ^ 2 / 4 := by
  filter_upwards [norm_condExp_exp_remainder_le hm hX hX2 hX3,
    hmean, hsecond, hthird] with ω hrem hmeanω hsecondω hthirdω
  simp only [Pi.zero_apply] at hmeanω
  rw [hmeanω] at hrem
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hrem
  exact norm_sub_gaussian_char_le hv hv₂
    (hrem.trans (mul_le_mul_of_nonneg_left hthirdω (by norm_num))) hsecondω

end Problem336.Innovation

end

end OAI
