import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex MeasureTheory Filter Asymptotics
open scoped FourierTransform Topology

def gaussianWave (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ)*b*(x : ℂ)^2)

theorem norm_gaussianWave (b : ℂ) (x : ℝ) :
    ‖gaussianWave b x‖=Real.exp (-Real.pi*b.re*x^2) := by
  unfold gaussianWave
  rw [show -(Real.pi : ℂ)*b*(x : ℂ)^2 = -((Real.pi : ℂ)*b)*(x : ℂ)^2 by ring,
    norm_cexp_neg_mul_sq]
  simp [Complex.mul_re]

theorem gaussianWave_decay {b : ℂ} (hb : 0<b.re) (s : ℝ) :
    gaussianWave b =o[cocompact ℝ] fun x : ℝ => |x|^s := by
  have hp : 0<((Real.pi : ℂ)*b).re := by simpa using mul_pos Real.pi_pos hb
  unfold gaussianWave
  simpa only [neg_mul] using isLittleO_exp_neg_mul_sq_cocompact hp s

theorem summable_gaussianWave {b : ℂ} (hb : 0<b.re) :
    Summable (fun n : ℤ => gaussianWave b (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ)<2))
    ((gaussianWave_decay hb (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite)

theorem fourier_gaussianWave {b : ℂ} (hb : 0<b.re) :
    𝓕 (gaussianWave b) = fun x : ℝ => (b^(1/2 : ℂ))⁻¹*gaussianWave b⁻¹ x := by
  have h := fourier_gaussian_pi hb
  unfold gaussianWave
  simpa only [one_div,div_eq_mul_inv,mul_assoc,one_mul] using h

theorem shifted_gaussian_poisson {b : ℂ} (hb : 0<b.re) (c : ℝ) :
    (∑' n : ℤ, gaussianWave b (c+n)) = (b^(1/2 : ℂ))⁻¹*
      ∑' n : ℤ, gaussianWave b⁻¹ n * fourier n (c : UnitAddCircle) := by
  have hn : b≠0 := by intro hzero; simp [hzero] at hb
  have hbi : 0<(b⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hn)
  have hF : (𝓕 (gaussianWave b)) =O[cocompact ℝ] fun x : ℝ => |x|^(-2 : ℝ) := by
    rw [fourier_gaussianWave hb]
    exact (gaussianWave_decay hbi (-2)).isBigO.const_mul_left _
  rw [Real.tsum_eq_tsum_fourier_of_rpow_decay
    (by unfold gaussianWave; fun_prop) (by norm_num : (1 : ℝ)<2)
    (gaussianWave_decay hb (-2)).isBigO hF c]
  simp_rw [fourier_gaussianWave hb,mul_assoc]
  exact tsum_mul_left

theorem dual_gaussian_tsum_tendsto {T : Type*} {l : Filter T} (b : T → ℂ)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) (c : ℝ) :
    Tendsto (fun t => ∑' n : ℤ, gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle))
      l (𝓝 1) := by
  have hfournorm (n : ℤ) : ‖fourier n (c : UnitAddCircle)‖=1 := Circle.norm_coe _
  have hbound : Summable (fun n : ℤ => Real.exp (-Real.pi*(n : ℝ)^2)) := by
    simpa only [norm_gaussianWave,Complex.one_re,mul_one] using
      (summable_gaussianWave (b := 1) (by norm_num)).norm
  suffices Tendsto (fun t => ∑' n : ℤ,
      gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle)) l
      (𝓝 (∑' n : ℤ, if n=0 then (1 : ℂ) else 0)) by simpa using this
  apply tendsto_tsum_of_dominated_convergence (f := fun t (n : ℤ) =>
      gaussianWave (b t)⁻¹ n * fourier n (c : UnitAddCircle))
      (g := fun n : ℤ => if n=0 then (1 : ℂ) else 0) hbound
  · intro n
    by_cases hn : n=0
    · subst n
      simpa [gaussianWave] using (tendsto_const_nhds (x := (1 : ℂ)) (f := l))
    · rw [ite_eq_right hn]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hsq : 0<(n : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
      have he := Real.tendsto_exp_atBot.comp
        (hRe.const_mul_atTop_of_neg (neg_lt_zero.mpr (mul_pos Real.pi_pos hsq)))
      convert he using 1
      funext t
      rw [norm_mul,norm_gaussianWave,hfournorm,mul_one]
      congr 1
      ring
  · filter_upwards [hRe.eventually (eventually_ge_atTop (1 : ℝ))] with t ht n
    rw [norm_mul,norm_gaussianWave,hfournorm,mul_one]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ht (sq_nonneg (n : ℝ))
    nlinarith [Real.pi_pos]

theorem normalized_shifted_gaussian_tendsto {T : Type*} {l : Filter T} (b : T → ℂ)
    (hb : ∀ᶠ t in l, 0<(b t).re)
    (hRe : Tendsto (fun t => ((b t)⁻¹).re) l atTop) (c : ℝ) :
    Tendsto (fun t => (b t)^(1/2 : ℂ)*∑' n : ℤ, gaussianWave (b t) (c+n)) l (𝓝 1) := by
  apply (dual_gaussian_tsum_tendsto b hRe c).congr'
  filter_upwards [hb] with t ht
  have hn : b t≠0 := by intro hzero; simp [hzero] at ht
  have hcp : (b t)^(1/2 : ℂ)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  rw [shifted_gaussian_poisson ht c,←mul_assoc,mul_inv_cancel₀ hcp,one_mul]

end Ostmann.QuadraticSieve

end

end OAI
