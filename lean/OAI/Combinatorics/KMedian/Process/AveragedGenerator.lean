import Mathlib
import OAI.Combinatorics.KMedian.Geometry.UniformDrift
import OAI.Combinatorics.KMedian.Process.GeneratorBound

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem averaged_ideal_drift (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
    (d N : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hqI0 : ∀ h i, 0 ≤ qI h i) (hqI : ∀ h i, qI h i ≤ 1)
    (hqE0 : ∀ h i, 0 ≤ qE h i) (hqE : ∀ h i, qE h i ≤ 1)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-Analytic.P x| ≤ ζ)
    (hcomp : ∀ i t, qI t i < 1 → N i*(1-pHat*qI t i) ≤ d i+d t)
    (hb : ∀ h, bH h ≤ b)
    (htaper : ∀ h i, 0 < qE h i → bH h ≤ d i+(1-pHat*qE h i)*N i)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      Analytic.B x*g*V+12*ζ*V := by
  let s := rowType (fun _ : H => g) (fun i h => qE h i)
  have hrow := row_type_bounds (fun _ : H => hg.le)
    (fun i h => hqE0 h i) (fun i h => hqE h i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => (hrow i).1
  have hs : ∀ i, s i ≤ 1 := fun i => (hrow i).2.1
  have hsEq : ∀ i, (∑ h, g*(qE h i)^2)=s i*(1-∑ t, g*qI t i) := by
    intro i
    have hh := (hrow i).2.2
    change s i*(∑ h, g*qE h i)=(∑ h, g*(qE h i)^2) at hh
    rw [hmass i] at hh
    exact hh.symm
  have hw0 : ∀ i, 0 ≤ ∑ t, g*qI t i := fun i =>
    Finset.sum_nonneg (fun t _ => mul_nonneg hg.le (hqI0 t i))
  have hw : ∀ i, (∑ t, g*qI t i) ≤ y := by
    intro i
    rw [← hysum]
    exact Finset.sum_le_sum (fun t _ => mul_le_of_le_one_right hg.le (hqI t i))
  have hincoming : ∀ i, (∑ h, g*qE h i) ≤ 1 := by
    intro i
    rw [hmass]
    linarith only [hw0 i]
  have hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i) := by
    intro i
    exact cap_average (fun _ => hg.le) (fun h => hqE0 h i) (hw i) hy
      (hmass i) (hsEq i) hb (fun h => htaper h i)
  have hK : ∀ i t, GraphMoments.kernel g qE i t ≤
      (s i*(1-∑ u, g*qI u i)+s t*(1-∑ u, g*qI u t))/2 := by
    intro i t
    have hh := GraphComparison.kernel_bound (q := fun i h => qE h i)
      (fun _ : H => hg.le) i t
    change GraphMoments.kernel g qE i t ≤
      ((∑ h, g*(qE h i)^2)+(∑ h, g*(qE h t)^2))/2 at hh
    simpa only [hsEq] using hh
  have hgeneration := expanded_bound (x := x) μ d N s bH XI XE qI qE hg.le hd hysum
    hmass hincoming hfirstI hfirstE hidem hpair hcap
  have hdrift := uniform_drift_le hg hx0 hx hysum hy hd hN hs0 hs
    (fun i t => hqI0 t i) (fun i t => hqI t i) hp0 hp hζ0 hζ he hcomp hK
  dsimp only at hgeneration ⊢
  linarith only [hgeneration, hdrift]

end MetricKMedian.GeneratorAverage
end
end

end OAI
