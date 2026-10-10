import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarReduction

namespace OAI

section
noncomputable section
open MeasureTheory Real
namespace SKRatio.Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def l2Norm (μ : Measure α) (f : α → ℝ) : ℝ := sqrt (∫ x, f x^2 ∂μ)

lemma l2Norm_nonneg (f : α → ℝ) : 0 ≤ l2Norm μ f := sqrt_nonneg _
lemma l2Norm_sq (f : α → ℝ) : l2Norm μ f^2 = ∫ x, f x^2 ∂μ :=
  sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))

lemma abs_integral_mul_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x*u x ∂μ| ≤ l2Norm μ f*l2Norm μ u := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hu)
  simp only [norm_eq_abs,Real.rpow_two,sq_abs,←sqrt_eq_rpow] at h
  have h' : |∫ x, f x*u x ∂μ| ≤ ∫ x, |f x| * |u x| ∂μ := by
    simpa only [abs_mul] using (abs_integral_le_integral_abs (f := fun x => f x*u x) (μ := μ))
  exact h'.trans h

lemma integral_mul_sq_le {f u : α → ℝ} (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    (∫ x, f x*u x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, u x^2 ∂μ) := by
  have h := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (l2Norm_nonneg f) (l2Norm_nonneg u))
    |>.mpr (abs_integral_mul_le hf hu)
  simpa only [sq_abs,mul_pow,l2Norm_sq] using h

lemma integral_pairing_add {f u z : α → ℝ}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, f x*(s*u x+t*z x) ∂μ =
      s*(∫ x, f x*u x ∂μ)+t*(∫ x, f x*z x ∂μ) := by
  have h1 : Integrable (fun x => f x*u x) μ := hf.integrable_mul hu
  have h2 : Integrable (fun x => f x*z x) μ := hf.integrable_mul hz
  have he (x : α) : f x*(s*u x+t*z x) = s*(f x*u x)+t*(f x*z x) := by ring
  simp_rw [he]
  rw [integral_add (h1.const_mul _) (h2.const_mul _),integral_const_mul,integral_const_mul]

lemma integral_square_add {u z : α → ℝ}
    (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) (s t : ℝ) :
    ∫ x, (s*u x+t*z x)^2 ∂μ =
      s^2*(∫ x, u x^2 ∂μ)+(2*s*t)*(∫ x, u x*z x ∂μ)+t^2*(∫ x, z x^2 ∂μ) := by
  have hpair : Integrable (fun x => u x*z x) μ := hu.integrable_mul hz
  have hsum : Integrable (fun x => s^2*u x^2+(2*s*t)*(u x*z x)) μ :=
    (hu.integrable_sq.const_mul _).add (hpair.const_mul _)
  have he (x : α) : (s*u x+t*z x)^2 = s^2*u x^2+(2*s*t)*(u x*z x)+t^2*z x^2 := by ring
  simp_rw [he]
  rw [integral_add hsum (hz.integrable_sq.const_mul _),
    integral_add (hu.integrable_sq.const_mul _) (hpair.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul]

theorem rank_two_bound {f u z : α → ℝ}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (hz : MemLp z 2 μ) :
    (∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ) ≤
      ((l2Norm μ u*l2Norm μ z+(∫ x, u x*z x ∂μ))/2)*(∫ x, f x^2 ∂μ) := by
  let U := l2Norm μ u
  let Z := l2Norm μ z
  have hU : 0 ≤ U := l2Norm_nonneg u
  have hZ : 0 ≤ Z := l2Norm_nonneg z
  have hU2 : (∫ x, u x^2 ∂μ) = U^2 := (l2Norm_sq u).symm
  have hZ2 : (∫ x, z x^2 ∂μ) = Z^2 := (l2Norm_sq z).symm
  have hfu := integral_mul_sq_le hf hu
  have hfz := integral_mul_sq_le hf hz
  have huz := integral_mul_sq_le hu hz
  rw [hU2] at hfu huz
  rw [hZ2] at hfz huz
  by_cases hzero : U*Z = 0
  · have hcross : (∫ x, u x*z x ∂μ) = 0 := by
      have hh : U^2*Z^2 = 0 := by nlinarith [sq_nonneg (U*Z)]
      rw [hh] at huz
      nlinarith only [huz,sq_nonneg (∫ x, u x*z x ∂μ)]
    have hprod : (∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ) = 0 := by
      rcases mul_eq_zero.mp hzero with hu0|hz0
      · rw [hu0] at hfu
        have hd : (∫ x, f x*u x ∂μ) = 0 := by nlinarith only [hfu,sq_nonneg (∫ x, f x*u x ∂μ)]
        rw [hd,zero_mul]
      · rw [hz0] at hfz
        have hd : (∫ x, f x*z x ∂μ) = 0 := by nlinarith only [hfz,sq_nonneg (∫ x, f x*z x ∂μ)]
        rw [hd,mul_zero]
    change _ ≤ ((U*Z+(∫ x, u x*z x ∂μ))/2)*_
    rw [hprod,hzero,hcross]
    simp
  · have hpos : 0 < U*Z := lt_of_le_of_ne (mul_nonneg hU hZ) (Ne.symm hzero)
    have hw : MemLp (fun x => Z*u x+U*z x) 2 μ :=
      (hu.const_mul Z).add (hz.const_mul U)
    have h := integral_mul_sq_le hf hw
    rw [integral_pairing_add hf hu hz,integral_square_add hu hz,hU2,hZ2] at h
    have hsq := sq_nonneg (Z*(∫ x, f x*u x ∂μ)-U*(∫ x, f x*z x ∂μ))
    apply (mul_le_mul_iff_of_pos_left (show 0 < 4*(U*Z) by positivity)).mp
    change 4*(U*Z)*((∫ x, f x*u x ∂μ)*(∫ x, f x*z x ∂μ)) ≤
      4*(U*Z)*(((U*Z+(∫ x, u x*z x ∂μ))/2)*(∫ x, f x^2 ∂μ))
    nlinarith only [h,hsq]

end Measure

section Probability
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def centered (μ : Measure ℝ) (f : ℝ → ℝ) (h : ℝ) : ℝ := f h-(∫ t, f t ∂μ)
def sd (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := l2Norm μ (centered μ f)

omit [IsProbabilityMeasure μ] in
lemma sd_nonneg (f : ℝ → ℝ) : 0 ≤ sd μ f := l2Norm_nonneg _

lemma memLp_centered {f : ℝ → ℝ} (hf : MemLp f 2 μ) : MemLp (centered μ f) 2 μ :=
  hf.sub (memLp_const _)

lemma integral_centered {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, centered μ f h ∂μ = 0 := by
  unfold centered
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _),integral_const]
  simp

lemma pairing_centered {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    ∫ h, f h*centered μ z h ∂μ = ∫ h, f h*z h ∂μ := by
  have hpair : Integrable (fun h => f h*z h) μ := hf.integrable_mul hz
  have he (h : ℝ) : f h*centered μ z h = f h*z h - f h*(∫ t, z t ∂μ) := by
    unfold centered
    ring
  simp_rw [he]
  rw [integral_sub hpair ((hf.integrable (by norm_num)).mul_const _),integral_mul_const,hmean]
  simp

lemma abs_pairing_centered_le {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    |∫ h, f h*z h ∂μ| ≤ l2Norm μ f*sd μ z := by
  have h := abs_integral_mul_le hf (memLp_centered hz)
  rwa [pairing_centered hf hz hmean] at h

lemma pairing_centered_sq_le {f z : ℝ → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ)
    (hmean : ∫ h, f h ∂μ = 0) :
    (∫ h, f h*z h ∂μ)^2 ≤ sd μ z^2*(∫ h, f h^2 ∂μ) := by
  have h := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (l2Norm_nonneg f) (sd_nonneg z))
    |>.mpr (abs_pairing_centered_le hf hz hmean)
  rw [sq_abs,mul_pow,l2Norm_sq] at h
  simpa only [mul_comm] using h

lemma l2_decomposition {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, f h^2 ∂μ = (∫ h, f h ∂μ)^2+(∫ h, centered μ f h^2 ∂μ) := by
  change ∫ h, f h^2 ∂μ = (∫ h, f h ∂μ)^2 + (∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ)
  rw [integral_centered_sq hf]
  ring

lemma integral_mul_decomposition {b z : ℝ → ℝ} (hb : MemLp b 2 μ) (hz : MemLp z 2 μ) :
    ∫ h, b h*z h ∂μ = (∫ h, b h ∂μ)*(∫ h, z h ∂μ) +
      (∫ h, centered μ b h*z h ∂μ) := by
  have hpair : Integrable (fun h => b h*z h) μ := hb.integrable_mul hz
  have hzI : Integrable z μ := hz.integrable (by norm_num)
  have he (h : ℝ) : centered μ b h*z h = b h*z h-(∫ t, b t ∂μ)*z h := by
    unfold centered
    ring
  simp_rw [he]
  rw [integral_sub hpair (hzI.const_mul _),integral_const_mul]
  ring

end Probability
end SKRatio.Scalar

end
end

end OAI
