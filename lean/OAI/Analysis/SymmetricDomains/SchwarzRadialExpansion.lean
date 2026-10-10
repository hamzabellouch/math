import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

def vanishingFactor : Space := 2-((AddMonoidAlgebra.single 1 1 : Poly) : Space)-
  ((AddMonoidAlgebra.single (-1) 1 : Poly) : Space)

lemma schwarzMode_nat (n : ℕ) (z : ℂ) :
    schwarzMode (n : ℤ) z = Complex.I*(2*z^n-1) := by
  cases n with
  | zero => norm_num [schwarzMode]
  | succ n => simp [schwarzMode]

lemma schwarzMode_second_difference (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    2*schwarzMode n z-schwarzMode (n+1) z-schwarzMode (n-1) z =
      (2-z-z⁻¹)*(schwarzMode n z-schwarzMode n 0)+
        (if n = 0 then 2*Complex.I*(1-z) else 0) := by
  by_cases hn : 0 < n
  · obtain ⟨m,hm⟩ : ∃ m : ℕ, n = ((m+1 : ℕ) : ℤ) := by
      refine ⟨n.toNat-1,?_⟩
      have hp : 0 < n.toNat := by omega
      have he : n.toNat-1+1 = n.toNat := Nat.sub_add_cancel hp
      rw [he,Int.toNat_of_nonneg hn.le]
    subst n
    have he1 : ((m+1 : ℕ) : ℤ)+1 = ((m+2 : ℕ) : ℤ) := by omega
    have he2 : ((m+1 : ℕ) : ℤ)-1 = (m : ℤ) := by omega
    rw [he1,he2,schwarzMode_nat,schwarzMode_nat,schwarzMode_nat,schwarzMode_nat]
    have hn0 : ((m+1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [ite_eq_right hn0]
    simp only [zero_pow (Nat.succ_ne_zero m),mul_zero,zero_sub,pow_succ]
    field_simp [hz]
    ring
  · by_cases hn0 : n = 0
    · subst n
      simp [schwarzMode]
      ring
    · have hn1 : ¬0 < n+1 := by omega
      have hn2 : ¬0 < n-1 := by omega
      simp only [schwarzMode,ite_eq_right hn,ite_eq_right hn1,ite_eq_right hn2,ite_eq_right hn0]
      ring

lemma vanishingFactor_mul_single (n : ℤ) (c : ℂ) :
    vanishingFactor*((AddMonoidAlgebra.single n c : Poly) : Space) =
      2*((AddMonoidAlgebra.single n c : Poly) : Space)-
      ((AddMonoidAlgebra.single (n+1) c : Poly) : Space)-
      ((AddMonoidAlgebra.single (n-1) c : Poly) : Space) := by
  simp only [vanishingFactor,sub_mul,single_mul,one_mul]
  rw [show 1+n = n+1 by omega,show -1+n = n-1 by omega]

lemma schwarz_vanishingFactor_mul (g : Space) {z : ℂ} (hz : z ∈ ClosedDisc) (hz0 : z ≠ 0) :
    discValue (vanishingFactor*g) z =
      (2-z-z⁻¹)*(discValue g z-discValue g 0)+2*Complex.I*(1-z)*coeff 0 g := by
  have h0 : (0 : ℂ) ∈ ClosedDisc := by simp [ClosedDisc]
  simp only [discValue_eq _ hz,discValue_eq _ h0]
  induction g using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p,Finset.mul_sum]
    simp only [map_sum,ContinuousMap.sum_apply]
    rw [← Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [vanishingFactor_mul_single,map_sub,map_sub]
    have h2 : schwarz (2*((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)) =
        (2 : ℂ) • schwarz ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space) := by
      simpa only [two_mul,two_smul] using schwarz.map_add
        ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)
        ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space)
    rw [h2]
    simp only [schwarz_single,coeff_single,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
      smul_eq_mul,schwarzModeC]
    have hh := schwarzMode_second_difference n hz0
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0] at hh
      rw [ite_eq_left hn0]
      linear_combination p.coeff n*hh
    · rw [ite_eq_right hn0] at hh
      rw [ite_eq_right hn0]
      linear_combination p.coeff n*hh

lemma schwarz_radial_expansion (g : Space) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    discValue (vanishingFactor*g) (1-(t : ℂ)) =
      2*Complex.I*(t : ℂ)*coeff 0 g -
        (t : ℂ)^2/(1-(t : ℂ))*(discValue g (1-(t : ℂ))-discValue g 0) := by
  have hz : (1-(t : ℂ)) ∈ ClosedDisc := by
    rw [Metric.mem_closedBall,dist_zero_right]
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1-t)]
    linarith
  have hz0 : (1-(t : ℂ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast ne_of_gt ht1
  rw [schwarz_vanishingFactor_mul g hz hz0]
  field_simp
  ring

end Release061.Wiener

end

end OAI
