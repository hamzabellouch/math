import OAI.NumberTheory.DirichletL.Hecke.Presentation
import OAI.NumberTheory.DirichletL.Hecke.DyadicBounded

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Complex
namespace SevenEighths.HeckeDyadicReflection
open HeckeFamily HeckePrimitive HeckeStripActual

variable (c : O) [NeZero c]

theorem functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    {s : ℂ} (hs : s.re<1) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s)/Complex.Gamma s) *
      LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  by_cases h0 : s=0
  · subst s
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    simp
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s≠0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s≠1 := by intro h; apply h0; linear_combination -h
  have hΓ : Complex.Gamma (1-s)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [LFunction_eq_uncompleted c χ hu hp hχ,he,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓ]
  have ha : ((HeckeStrip.completionScale (conductor c)) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have hpow : (HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)=
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) := by
    rw [←Complex.cpow_add _ _ ha]
    congr 1
    ring
  rw [div_eq_mul_inv]
  calc
    _ = TraceCharacter.normalizedGauss c χ *
        ((HeckeStrip.completionScale (conductor c) : ℂ)^(-s)*
          (HeckeStrip.completionScale (conductor c) : ℂ)^(1-s)) *
        (Complex.Gamma (1-s)*(Complex.Gamma s)⁻¹) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by ring
    _ = _ := by rw [hpow]

theorem gamma_real_ratio_bound : ∃ C : ℝ, 0<C ∧
    ∀ x ∈ Icc (-(1/10 : ℝ)) (1/2), Real.Gamma (1-x)/Real.Gamma (x+2)≤C := by
  have hcont : ContinuousOn (fun x : ℝ => Real.Gamma (1-x)/Real.Gamma (x+2))
      (Icc (-(1/10 : ℝ)) (1/2)) := by
    intro x hx
    have hnum : DifferentiableAt ℝ Real.Gamma (1-x) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.2])
    have hden : DifferentiableAt ℝ Real.Gamma (x+2) :=
      Real.differentiableAt_Gamma (by intro n hn; have hnn := Nat.cast_nonneg (α:=ℝ) n; linarith [hx.1])
    exact ((hnum.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => 1-y) (show ContinuousAt (fun y : ℝ => 1-y) x by fun_prop)).div
      (hden.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => y+2) (show ContinuousAt (fun y : ℝ => y+2) x by fun_prop))
      (Real.Gamma_pos_of_pos (show 0<x+2 by linarith [hx.1])).ne').continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))

theorem gamma_ratio_strip_bound : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ,
    -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖Complex.Gamma (1-s)/Complex.Gamma s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hreal⟩ := gamma_real_ratio_bound
  refine ⟨C,hC,?_⟩
  intro s hl hr
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1/2) (1/2-s.re) (-s.im) 2 (by linarith) (by norm_num; linarith)
  have hnum : ((1/2 : ℝ) : ℂ)+((1/2-s.re : ℝ)+(-s.im)*I)=1-s := by
    apply Complex.ext <;> simp; ring
  have hden : ((1/2 : ℝ) : ℂ)-((1/2-s.re : ℝ)+(-s.im)*I)+(2 : ℕ)=s+2 := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hb
  rw [hnum,hden] at hb
  have hreal' := hreal s.re ⟨hl,hr⟩
  have hb' : ‖Complex.Gamma (1-s)/Complex.Gamma (s+2)‖≤C := by
    apply hb.trans
    convert hreal' using 1; congr 1 <;> ring_nf
  have heq : Complex.Gamma (1-s)/Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s+k))*(Complex.Gamma (1-s)/Complex.Gamma (s+2)) := by
    rw [div_eq_mul_inv,CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat,div_eq_mul_inv]
    ring
  have hs : ‖s‖≤1+|s.im| := by
    have hsr : |s.re|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hn := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  norm_num only [Nat.cast_ofNat] at hf
  have hf' : ‖∏ k ∈ Finset.range 2,(s+k)‖≤(3+|s.im|)^2 :=
    hf.trans (pow_le_pow_left₀ (by positivity) (show ‖s‖+2≤3+|s.im| by linarith) 2)
  rw [heq,norm_mul]
  exact (mul_le_mul hf' hb' (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem completionScale_rpow_le {Q x : ℝ} (hQ : 0<Q) (hx : 0≤x) :
    HeckeStrip.completionScale Q ^ x≤Q^(x/2) := by
  have hs3 : Real.sqrt 3≤2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hscale : HeckeStrip.completionScale Q≤Real.sqrt Q := by
    unfold HeckeStrip.completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ)≤3)]
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [Real.sqrt_nonneg Q,Real.pi_gt_three]
  calc
    _ ≤ (Real.sqrt Q)^x := Real.rpow_le_rpow
      (HeckeStrip.completionScale_pos Q hQ).le hscale hx
    _ = _ := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hQ.le]
      congr 1
      ring

theorem primitive_reflected_bound : ∃ C : ℝ, 0<C ∧
    ∀ (c : O) [NeZero c] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O))=1)
      (_hp : FiniteFourier.IsPrimitiveOnIdeals χ), χ≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤s.re → s.re≤1/2 →
    ‖LFunction (character c χ hu) s‖≤
      C*(conductor c)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ := by
  obtain ⟨C,hC,hgamma⟩ := gamma_ratio_strip_bound
  refine ⟨C,hC,?_⟩
  intro c _ χ hu hp hχ s hl hr
  rw [functional_equation c χ hu hp hχ (by linarith),norm_mul,norm_mul,norm_mul,
    TraceCharacter.normalizedGauss_norm c χ hp,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)))]
  have hscale := completionScale_rpow_le
    (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)) (show 0≤1-2*s.re by linarith)
  have he : (1-2*s).re=1-2*s.re := by simp
  rw [he]
  have he' : (1-2*s.re)/2=1/2-s.re := by ring
  rw [he'] at hscale
  calc
    _ ≤ ((conductor c)^(1/2-s.re)*(C*(3+|s.im|)^2))*
        ‖LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hscale (hgamma s hl hr)
        (norm_nonneg _) (Real.rpow_nonneg (by exact_mod_cast (conductor_ge_one c).trans' zero_le_one) _))
        (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.HeckeDyadicReflection

end

end OAI
