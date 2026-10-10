import OAI.Combinatorics.HoneycombChords.FiniteFunctional
import OAI.Combinatorics.HoneycombChords.BetaKernel

namespace OAI

/-! Calculus of the entire cosine continuation on the real line. -/

section
namespace CriticalHoneycomb.FiniteFunctional
open Real Filter Topology MeasureTheory
open Analytic
lemma C_sq (t : ℝ) {z : ℝ} (hz : 0 ≤ z) : C t (z^2)=(Real.cosh (t*z):ℂ) := by
  simp [C,sq_nonneg,Real.sqrt_sq hz]
lemma C_zero (t : ℝ) : C t 0=1 := by simp [C]
lemma C_neg_four (t : ℝ) : C t (-4)=(Real.cos (2*t):ℂ) := by
  norm_num [C,mul_comm]
lemma C_contDiff (x : ℝ) : ContDiff ℝ ⊤ (fun t => C t x) := by
  unfold C
  split_ifs
  · exact Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ⊤ (fun t : ℝ => Real.cosh (t*Real.sqrt x)) by fun_prop)
  · exact Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (t*Real.sqrt (-x))) by fun_prop)
lemma hypJet_succ_zero (j : ℕ) : hypJet (j+1) 0=(1+(-1:ℝ)^j)/2 := by
  simp only [hypJet,Real.exp_zero,neg_zero,mul_one,pow_succ];ring
lemma C_sq_jet (j : ℕ) (t : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    iteratedDeriv j (fun u => C u (z^2)) t=(z^j*hypJet (j+1) (t*z):ℝ) := by
  induction j generalizing t with
  | zero => simp [C_sq _ hz]
  | succ j ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv j (fun u => C u (z^2))=
      (fun u => ((z^j*hypJet (j+1) (u*z):ℝ):ℂ)) from funext ih]
    have hd := ((hypJet_hasDerivAt (j+1) (t*z)).comp t ((hasDerivAt_id t).mul_const z)).const_mul (z^j)
    have he:=hd.ofReal_comp.deriv
    change deriv (fun u => ((z^j*hypJet (j+1) (u*z):ℝ):ℂ)) t = _ at he
    rw [he]
    congr 1
    rw [pow_succ]
    ring
lemma angle_pos : 0 < angle := by unfold angle;positivity
lemma D_sq {z : ℝ} (hz : 0 ≤ z) : D (z^2)=(2*Real.cosh (angle*z)-1:ℝ) := by
  simp only [D,C_sq _ hz];push_cast;rfl
lemma D_sq_ne_zero {z : ℝ} (hz : 0 ≤ z) : D (z^2) ≠ 0 := by
  rw [D_sq hz]
  apply Complex.ofReal_ne_zero.mpr
  have h:=Real.one_le_cosh (angle*z)
  linarith
lemma g_sq {z : ℝ} (hz : 0 < z) : g (z^2)=(Real.sinh (angle*z)/z:ℝ) := by
  unfold g
  simp only [C_sq _ hz.le]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have hd (t : ℝ) : HasDerivAt (fun t => Real.sinh (t*z)/z) (Real.cosh (t*z)) t := by
    convert (((Real.hasDerivAt_sinh (t*z)).comp t ((hasDerivAt_id t).mul_const z)).div_const z) using 1 <;> try rfl
    field_simp
  have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=angle) (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => Real.cosh (t*z)) by fun_prop).intervalIntegrable 0 angle)
  simpa using he
end CriticalHoneycomb.FiniteFunctional

end

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic

lemma cosineKernelJet_eq_C {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    (cosineKernelJet 0 0 b x:ℂ)=C (Real.sqrt b) x := by
  by_cases hx : 0 ≤ x
  · rw [cosineKernelJet_zero_zero_cosh hb hx,C,ite_eq_left hx]
  · rw [cosineKernelJet_zero_zero_cos hb (le_of_not_ge hx),C,ite_eq_right hx]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end OAI
