import Mathlib.Tactic.ComputeDegree
import OAI.MathematicalPhysics.Transonic.Exterior.Polynomial
import OAI.MathematicalPhysics.Transonic.Exterior.SourceTrace

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Polynomial

def residual (h sigma kappa c : ℝ) (w : ℝ[X]) : ℝ[X] :=
  (1-C h*X)*(1-C sigma*(1-C h*X)^2)*(2*w-w^2)*derivative w-
    C h*(C (1-c)+2*C c*w-C c*w^2)*
      (C kappa*(1-C h*X)*(2*w-w^2)+3*(w-C h*X))

lemma coe_residual (h sigma kappa c : ℝ) (w : ℝ[X]) :
    ((residual h sigma kappa c w : ℝ[X]) : PowerSeries ℝ)=
      ExteriorJet.scaledResidual h sigma kappa c w := by
  rw [ExteriorJet.scaledResidual_expansion]
  have hn (n : ℕ) : ((n : ℝ[X]) : PowerSeries ℝ)=n := by
    rw [← coeToPowerSeries.ringHom_apply,map_natCast]
  simp only [residual,coe_mul,coe_sub,coe_add,coe_pow,coe_one,coe_C,coe_X,
    PowerSeries.derivative_coe]
  rw [show (((2:ℝ[X]):PowerSeries ℝ))=2 from hn 2,
    show (((3:ℝ[X]):PowerSeries ℝ))=3 from hn 3]

lemma eval_residual (h sigma kappa c : ℝ) (w : ℝ[X]) (x : ℝ) :
    (residual h sigma kappa c w).eval x=
      (1-h*x)*(1-sigma*(1-h*x)^2)*(2*w.eval x-(w.eval x)^2)*deriv (fun t => w.eval t) x-
        h*((1-c)+2*c*w.eval x-c*(w.eval x)^2)*
          (kappa*(1-h*x)*(2*w.eval x-(w.eval x)^2)+3*(w.eval x-h*x)) := by
  simp [residual,Polynomial.deriv]

lemma degree_residual (h sigma kappa c : ℝ) (w : ℝ[X]) (hw : w.natDegree≤73) :
    (residual h sigma kappa c w).natDegree≤293 := by
  have hd := natDegree_derivative_le w
  unfold residual
  compute_degree!
  omega

lemma trunc_congr (f : PowerSeries ℝ) (m : ℕ) :
    (PowerSeries.X : PowerSeries ℝ)^m ∣ f-(PowerSeries.trunc m f : PowerSeries ℝ) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub,Polynomial.coeff_coe,PowerSeries.coeff_trunc]
  simp [hn]

lemma residual_lowzero (h sigma kappa c : ℝ) (f : PowerSeries ℝ)
    (hf0 : PowerSeries.coeff 0 f=0) (hf : ExteriorJet.scaledResidual h sigma kappa c f=0)
    (n : ℕ) (hn : n<74) : (residual h sigma kappa c (PowerSeries.trunc 74 f)).coeff n=0 := by
  have hh := ExteriorJet.scaledResidual_congr h sigma kappa c f (PowerSeries.trunc 74 f) 74
    (by norm_num) hf0 (trunc_congr f 74)
  rw [hf,zero_sub,← coe_residual] at hh
  have hh' := PowerSeries.X_pow_dvd_iff.mp hh n hn
  simpa using hh'

lemma eval_factor (p : ℝ[X]) (hp : p.natDegree≤293)
    (hz : ∀ n<74, p.coeff n=0) (x : ℝ) :
    p.eval x=x^74*∑ i ∈ Finset.range 220, p.coeff (i+74)*x^i := by
  rw [eval_eq_sum_range' (show p.natDegree<294 by omega),
    show 294=74+220 by norm_num,Finset.sum_range_add]
  have hzero : ∑ i ∈ Finset.range 74, p.coeff i*x^i=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i (Finset.mem_range.mp hi),zero_mul]
  rw [hzero,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add,Nat.add_comm 74 i]
  ring

lemma root_exists (b A : ℝ) (hb : 0<b) (hA : 0<A) : ∃ d:ℝ, 0<d ∧ b*d^73=A := by
  refine ⟨(A/b)^((73:ℝ)⁻¹),Real.rpow_pos_of_pos (div_pos hA hb) _,?_⟩
  have hp := Real.rpow_inv_natCast_pow (div_pos hA hb).le (by norm_num : (73:ℕ)≠0)
  norm_num only [Nat.cast_ofNat] at hp
  simp only [one_div] at hp
  rw [hp]
  exact mul_div_cancel₀ A (ne_of_gt hb)

lemma scaled_full_equation (sigma kappa c d : ℝ) (u : PowerSeries ℝ)
    (he : Formal.residual sigma kappa c u=0) :
    ExteriorJet.scaledResidual (-d/256) sigma kappa c
      (PowerSeries.rescale (-d) (ExteriorJet.scaledReflected u))=0 := by
  rw [ExteriorJet.scaledReflected,PowerSeries.rescale_rescale,
    show (1/256:ℝ)*(-d)= -d/256 by ring,
    ExteriorJet.scaledResidual_rescale,ExteriorJet.reflected_equation _ _ _ _ he]
  simp

end SepticProfile.ExteriorPolynomial

end
end

end OAI
