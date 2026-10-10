import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationGaussian

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex Filter
open scoped Topology

def gaussParameter (q : ℕ) (ε : ℝ) : ℂ := (ε : ℂ)-(2/(q : ℂ))*I

def gaussResidual (q : ℕ) (ε : ℝ) : ℂ := (gaussParameter q ε)⁻¹-((q : ℂ)/2)*I

def gaussResidualRatio (q : ℕ) (ε : ℝ) : ℂ :=
  ((q : ℂ)^2/4)/(1+((q : ℂ)*(ε : ℂ)/2)*I)

@[simp] theorem gaussParameter_re (q : ℕ) (ε : ℝ) : (gaussParameter q ε).re=ε := by
  simp [gaussParameter,Complex.div_re]

theorem gaussParameter_ne_zero (q : ℕ) [NeZero q] (ε : ℝ) : gaussParameter q ε≠0 := by
  have hq : (q : ℝ)≠0 := by exact_mod_cast NeZero.ne q
  intro h
  have hi := congrArg Complex.im h
  simp [gaussParameter,Complex.div_re] at hi
  exact NeZero.ne q hi

theorem gaussResidualRatio_den_ne_zero (q : ℕ) (ε : ℝ) :
    1+((q : ℂ)*(ε : ℂ)/2)*I≠0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.div_re] at hr

theorem gaussResidual_eq_mul_ratio (q : ℕ) [NeZero q] (ε : ℝ) :
    gaussResidual q ε = (ε : ℂ)*gaussResidualRatio q ε := by
  have hq : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hz := gaussParameter_ne_zero q ε
  have hr := gaussResidualRatio_den_ne_zero q ε
  unfold gaussResidual gaussResidualRatio
  conv_rhs => rw [←mul_div_assoc]
  apply (eq_div_iff hr).2
  field_simp [hz]
  unfold gaussParameter
  field_simp
  ring_nf
  have hI3 : Complex.I^(3 : ℕ) = -Complex.I := by
    calc
      Complex.I^3 = Complex.I^2*Complex.I := by ring
      _ = -Complex.I := by rw [I_sq]; ring
  simp only [hI3,I_sq]
  ring

theorem gaussResidualRatio_re_pos (q : ℕ) [NeZero q] (ε : ℝ) :
    0<(gaussResidualRatio q ε).re := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have hr := gaussResidualRatio_den_ne_zero q ε
  have hden := Complex.normSq_pos.mpr hr
  have hre : (gaussResidualRatio q ε).re = ((q : ℝ)^2/4)/
      Complex.normSq (1+((q : ℂ)*(ε : ℂ)/2)*I) := by
    unfold gaussResidualRatio
    have hs : (q : ℂ)^2=(((q : ℝ)^2 : ℝ) : ℂ) := by norm_cast
    have hsre : ((q : ℂ)^2).re=(q : ℝ)^2 := congrArg Complex.re hs
    have hsim : ((q : ℂ)^2).im=0 := congrArg Complex.im hs
    simp [Complex.div_re,Complex.mul_re,hsre,hsim]
  rw [hre]
  exact div_pos (by positivity) hden

theorem gaussResidual_re_pos (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0<ε) :
    0<(gaussResidual q ε).re := by
  rw [gaussResidual_eq_mul_ratio,Complex.re_ofReal_mul]
  exact mul_pos hε (gaussResidualRatio_re_pos q ε)

theorem gaussResidual_inv (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0<ε) :
    (gaussResidual q ε)⁻¹=4/((q : ℂ)^2*(ε : ℂ))+(2/(q : ℂ))*I := by
  have hq : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have he : (ε : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hε.ne'
  rw [gaussResidual_eq_mul_ratio]
  unfold gaussResidualRatio
  field_simp
  ring

theorem gaussResidual_inv_re (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0<ε) :
    ((gaussResidual q ε)⁻¹).re=4/((q : ℝ)^2*ε) := by
  rw [gaussResidual_inv q hε]
  have hs : (q : ℂ)^2=(((q : ℝ)^2 : ℝ) : ℂ) := by norm_cast
  rw [hs]
  simp only [←Complex.ofReal_mul,←Complex.ofReal_ofNat,←Complex.ofReal_natCast,
    ←Complex.ofReal_div,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]

theorem tendsto_gaussResidual_inv_re (q : ℕ) [NeZero q] :
    Tendsto (fun ε : ℝ => ((gaussResidual q ε)⁻¹).re) (𝓝[>] (0 : ℝ)) atTop := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop
    (show (0 : ℝ)<4/(q : ℝ)^2 by positivity)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [gaussResidual_inv_re q hε]
  ring

theorem gaussResidualRatio_continuousAt_zero (q : ℕ) :
    ContinuousAt (gaussResidualRatio q) 0 := by
  unfold gaussResidualRatio
  exact continuousAt_const.div (by fun_prop) (gaussResidualRatio_den_ne_zero q 0)

end Ostmann.QuadraticSieve

end

end OAI
