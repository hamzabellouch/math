import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationParameters

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex Filter
open scoped Topology

theorem principal_sqrt_sq (b : ℂ) : (b^(1/2 : ℂ))^2=b := by
  rw [←Complex.cpow_mul_nat]
  norm_num

theorem principal_sqrt_re_pos {b : ℂ} (hb : 0<b.re) : 0<(b^(1/2 : ℂ)).re := by
  rw [one_div,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos_of_pos
  linarith [norm_nonneg b]

theorem principal_sqrt_mul_real {t : ℝ} (ht : 0<t) {b : ℂ} (hb : 0<b.re) :
    ((t : ℂ)*b)^(1/2 : ℂ)=(Real.sqrt t : ℂ)*b^(1/2 : ℂ) := by
  have hy : 0<((Real.sqrt t : ℂ)*b^(1/2 : ℂ)).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos (Real.sqrt_pos_of_pos ht) (principal_sqrt_re_pos hb)
  have hs : ((Real.sqrt t : ℂ)*b^(1/2 : ℂ))^2=(t : ℂ)*b := by
    rw [mul_pow,principal_sqrt_sq]
    have h : (Real.sqrt t : ℂ)^2=(t : ℂ) := by exact_mod_cast Real.sq_sqrt ht.le
    rw [h]
  rw [←hs]
  simpa only [one_div] using Complex.sq_cpow_two_inv hy

theorem principal_sqrt_ofReal {t : ℝ} (ht : 0<t) :
    (t : ℂ)^(1/2 : ℂ)=(Real.sqrt t : ℂ) := by
  have hs : (Real.sqrt t : ℂ)^2=(t : ℂ) := by exact_mod_cast Real.sq_sqrt ht.le
  rw [←hs,one_div,Complex.sq_cpow_two_inv (by simpa using Real.sqrt_pos_of_pos ht)]

theorem principal_sqrt_gaussParameter_zero (q : ℕ) [NeZero q] :
    (gaussParameter q 0)^(1/2 : ℂ)=(1-I)/(Real.sqrt (q : ℝ) : ℂ) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have hqc : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hs : (Real.sqrt (q : ℝ) : ℂ)^2=(q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  have hsn : (Real.sqrt (q : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hq).ne'
  have hy : 0<((1-I)/(Real.sqrt (q : ℝ) : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    simpa using one_div_pos.mpr (Real.sqrt_pos_of_pos hq)
  have hy2 : ((1-I)/(Real.sqrt (q : ℝ) : ℂ))^2=gaussParameter q 0 := by
    rw [div_pow,hs]
    unfold gaussParameter
    simp only [Complex.ofReal_zero,zero_sub]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [←hy2,one_div,Complex.sq_cpow_two_inv hy]

def gaussNormalizationRatio (q : ℕ) (ε : ℝ) : ℂ :=
  (q : ℂ)*((gaussParameter q ε)^(1/2 : ℂ))⁻¹ /
    ((gaussResidualRatio q ε*16)^(1/2 : ℂ))

theorem gaussNormalizationRatio_continuousAt_zero (q : ℕ) [NeZero q] :
    ContinuousAt (gaussNormalizationRatio q) 0 := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have hz : (gaussParameter q 0)∈Complex.slitPlane := by
    right
    have hz0 : gaussParameter q 0≠0 := gaussParameter_ne_zero q 0
    intro hi
    apply hz0
    apply Complex.ext
    · simp
    · simpa using hi
  have hroot : ContinuousAt (fun ε : ℝ => (gaussParameter q ε)^(1/2 : ℂ)) 0 :=
    ContinuousAt.comp (x := (0 : ℝ)) (f := gaussParameter q)
      (continuousAt_cpow_const hz) (by unfold gaussParameter; fun_prop)
  have hzroot : (gaussParameter q 0)^(1/2 : ℂ)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (gaussParameter_ne_zero q 0))
  have hrpos : 0<(gaussResidualRatio q 0*16).re := by
    simpa using mul_pos (gaussResidualRatio_re_pos q 0) (by norm_num : (0 : ℝ)<16)
  have hrr : ContinuousAt (fun ε : ℝ => (gaussResidualRatio q ε*16)^(1/2 : ℂ)) 0 :=
    ContinuousAt.comp (x := (0 : ℝ)) (f := fun ε => gaussResidualRatio q ε*16)
      (continuousAt_cpow_const (Or.inl hrpos))
      ((gaussResidualRatio_continuousAt_zero q).mul continuousAt_const)
  have hrne : gaussResidualRatio q 0*16≠0 := by intro h; simp [h] at hrpos
  exact (continuousAt_const.mul (hroot.inv₀ hzroot)).div hrr
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hrne))

theorem gaussNormalizationRatio_zero (q : ℕ) [NeZero q] :
    gaussNormalizationRatio q 0=(Real.sqrt (q : ℝ) : ℂ)*(1+I)/4 := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have hqc : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hs : (Real.sqrt (q : ℝ) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hq).ne'
  have hi : (1-I : ℂ)≠0 := by intro h; have := congrArg Complex.re h; norm_num at this
  have hr : gaussResidualRatio q 0*16=(2*(q : ℂ))^2 := by
    simp [gaussResidualRatio]
    ring
  have hp : 0<(2*(q : ℂ)).re := by simpa using (mul_pos (by norm_num : (0 : ℝ)<2) hq)
  unfold gaussNormalizationRatio
  rw [principal_sqrt_gaussParameter_zero,hr,one_div,Complex.sq_cpow_two_inv hp]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

end Ostmann.QuadraticSieve

end

end OAI
