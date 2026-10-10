import Mathlib
import OAI.Combinatorics.KMedian.Geometry.MomentAnalysis
import OAI.Combinatorics.KMedian.Process.GeneratorAverage

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem expanded_bound (μ : FiniteLaw Ω) {g x y pHat b : ℝ}
    (d N s : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i, 0 ≤ d i) (hysum : ∑ _i : I, g=y)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hincoming : ∀ i, ∑ h, g*qE h i ≤ 1)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t)
    (hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i)
        (GraphMoments.kernel g qE) x y pHat+Analytic.B x*g*V := by
  dsimp only
  let V := ∑ i, g*d i
  let w := fun i => ∑ t, g*qI t i
  let a := coefficient x y
  let B := Analytic.B x
  let K := GraphMoments.kernel g qE
  let C := ∑ i, g*((y-w i)*(d i+(1-pHat*s i)*N i))
  let Wd := ∑ i, g*w i*d i
  let W := ∑ i, g*w i
  let Q := ∑ i, ∑ t, g^2*K i t*d t
  let Hinge := ∑ i, g*(∑ t, g*(1-qI t i)*max (d t-a*d i) 0)
  have hB : 0 ≤ B := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (P_nonneg x)
  have hcost : (∑ i, g*d i*(∑ h, g*qE h i))=V-Wd := by
    simp_rw [hmass]
    dsimp only [V, Wd, w]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmass' : (∑ i, g*(∑ h, g*qE h i))=y-W := by
    simp_rw [hmass, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hysum]
  have hcap' : (∑ i, g*(∑ h, g*qE h i*bH h)) ≤ y*(1-y)*b+C := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hcap i) hg)
    have heq : (∑ i, g*((1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i))) =
        y*(1-y)*b+C := by
      rw [show (fun i => g*((1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i))) =
          fun i => g*((1-y)*b)+g*((y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) by
        funext i; ring, Finset.sum_add_distrib, ← Finset.sum_mul, hysum]
      dsimp only [C, w]
      ring
    exact hh.trans_eq heq
  have hquad : μ.expect (fun ω => ∑ h, g*removedMass g XE ω h*removedCost g d XE ω h) ≤ Q+g*V := by
    rw [quadratic_identity μ g d XE qE hidem hfirstE hpair]
    exact add_le_add (le_refl Q) (diagonal_bound hg d qE hd hincoming)
  have hext : μ.expect (external g a B V bH d XE) ≤
      y*(1-y)*b+C-a*(V-Wd)-B*V*(y-W)+B*(Q+g*V) := by
    rw [external_mean_split μ g a B V bH d XE qE hfirstE, hcost, hmass']
    exact add_le_add (sub_le_sub_right (sub_le_sub_right hcap' _) _)
      (mul_le_mul_of_nonneg_left hquad hB)
  have hin := inside_mean μ g a (a*V+(1-y)*b) d XI qI hfirstI
  rw [hysum] at hin
  change μ.expect (inside g a (a*V+(1-y)*b) d XI)=V-y*(a*V+(1-y)*b)-Hinge at hin
  have hdecomp := drift_decomposition g x y pHat d N s (fun i t => qI t i) K
  change unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat =
    -(3*y+B*(y-x)^2)*V+C+(1+m x+B*y)*Wd+B*V*W+B*Q-
      ∑ i, g*(∑ t, g*(1-qI t i)*max (d t-(1+m x+B*y)*d i) 0) at hdecomp
  have ha : a=1+m x+B*y := coefficient_eq x y
  rw [← ha] at hdecomp
  change unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat =
    -(3*y+B*(y-x)^2)*V+C+a*Wd+B*V*W+B*Q-Hinge at hdecomp
  have hc := coefficient_identity_drift x y
  change (1+y)*a+y*B-2*x*(y-x)*moment 2 x-1=3*y+B*(y-x)^2 at hc
  change 2*x*(y-x)*moment 2 x*V+
    μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+external g a B V bH d XE ω) ≤
    unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i) K x y pHat+B*g*V
  rw [μ.expect_add, hin, hdecomp]
  have hscaled := congrArg (fun z => z*V) hc
  nlinarith only [hext, hscaled]

end MetricKMedian.GeneratorAverage
end
end

end OAI
