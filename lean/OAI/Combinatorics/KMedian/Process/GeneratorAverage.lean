import Mathlib
import OAI.Combinatorics.KMedian.Geometry.GraphMoments
import OAI.Combinatorics.KMedian.Process.AveragedDrift

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def inside (g a f : ℝ) (d : I → ℝ) (X : Ω → I → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(d h-(∑ i, g*(1-X ω h i)*max (d h-a*d i) 0)-f)
noncomputable def outside (g a B V : ℝ) (bH d : I → ℝ) (X : Ω → I → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(removedMass g X ω h*bH h-a*removedCost g d X ω h-
    B*removedMass g X ω h*(V-removedCost g d X ω h))
noncomputable def external (g a B V : ℝ) (bH : H → ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(removedMass g X ω h*bH h-a*removedCost g d X ω h-
    B*removedMass g X ω h*(V-removedCost g d X ω h))

omit [Fintype H] [DecidableEq I] in
theorem inside_mean (μ : FiniteLaw Ω) (g a f : ℝ) (d : I → ℝ)
    (X : Ω → I → I → ℝ) (q : I → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) :
    μ.expect (inside g a f d X) =
      (∑ i, g*d i)-(∑ _i : I, g)*f-
      ∑ i, g*(∑ t, g*(1-q t i)*max (d t-a*d i) 0) := by
  change μ.expect (fun ω => inside g a f d X ω)=_
  simp only [inside, μ.expect_sum, μ.expect_mul, μ.expect_sub, μ.expect_const,
    μ.expect_mul_right, hfirst]
  have htranspose : (∑ h, g*(∑ i, g*(1-q h i)*max (d h-a*d i) 0)) =
      ∑ i, g*(∑ t, g*(1-q t i)*max (d t-a*d i) 0) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have ht : (∑ h, g*∑ i, (g*1-g*q h i)*max (d h-a*d i) 0) =
      ∑ i, g*∑ t, (g*1-g*q t i)*max (d t-a*d i) 0 := by
    simpa only [mul_sub] using htranspose
  rw [ht]
  ring

omit [Fintype H] [DecidableEq I] in
theorem mass_mean (μ : FiniteLaw Ω) (g : ℝ) (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) (h : H) :
    μ.expect (fun ω => removedMass g X ω h)=∑ i, g*q h i := by
  simp only [removedMass, μ.expect_sum, μ.expect_mul, hfirst]

omit [Fintype H] [DecidableEq I] in
theorem cost_mean (μ : FiniteLaw Ω) (g : ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) (h : H) :
    μ.expect (fun ω => removedCost g d X ω h)=∑ i, g*d i*q h i := by
  simp only [removedCost, μ.expect_sum, μ.expect_mul, hfirst]

omit [DecidableEq I] in
theorem external_mean_split (μ : FiniteLaw Ω) (g a B V : ℝ) (bH : H → ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (q : H → I → ℝ)
    (hfirst : ∀ h i, μ.expect (fun ω => X ω h i)=q h i) :
    μ.expect (external g a B V bH d X) =
      (∑ i, g*(∑ h, g*q h i*bH h))-
      a*(∑ i, g*d i*(∑ h, g*q h i))-
      B*V*(∑ i, g*(∑ h, g*q h i))+
      B*μ.expect (fun ω => ∑ h, g*removedMass g X ω h*removedCost g d X ω h) := by
  have hp : ∀ ω, external g a B V bH d X ω =
      (∑ h, g*removedMass g X ω h*bH h)-
      a*(∑ h, g*removedCost g d X ω h)-
      B*V*(∑ h, g*removedMass g X ω h)+
      B*(∑ h, g*removedMass g X ω h*removedCost g d X ω h) := by
    intro ω
    simp only [external, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  change μ.expect (fun ω => external g a B V bH d X ω)=_
  simp only [hp, μ.expect_add, μ.expect_sub, μ.expect_mul,
    μ.expect_sum, μ.expect_mul_right, mass_mean μ g X q hfirst,
    cost_mean μ g d X q hfirst]
  have hcap : (∑ h, g*(∑ i, g*q h i)*bH h)=∑ i, g*(∑ h, g*q h i*bH h) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    ring
  have hcost : (∑ h, g*(∑ i, g*d i*q h i))=∑ i, g*d i*(∑ h, g*q h i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    ring
  have hmass : (∑ h, g*(∑ i, g*q h i))=∑ i, g*(∑ h, g*q h i) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hcap, hcost, hmass]

omit [Fintype Ω] [Fintype H] [DecidableEq I] in
theorem drift_decomposition (g x y pHat : ℝ) (d N s : I → ℝ) (q K : I → I → ℝ) :
    let V := ∑ i, g*d i
    let w := fun i => ∑ t, g*q i t
    let a := 1+m x+Analytic.B x*y
    unnormalizedDrift (fun _ => g) d N s q K x y pHat =
      -(3*y+Analytic.B x*(y-x)^2)*V+
      (∑ i, g*((y-w i)*(d i+(1-pHat*s i)*N i)))+
      a*(∑ i, g*w i*d i)+Analytic.B x*V*(∑ i, g*w i)+
      Analytic.B x*(∑ i, ∑ t, g^2*K i t*d t)-
      ∑ i, g*(∑ t, g*(1-q i t)*max (d t-a*d i) 0) := by
  dsimp only
  unfold unnormalizedDrift
  dsimp only
  have hterm : ∀ i,
      g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i)+
        (1+m x+Analytic.B x*y)*(∑ t, g*q i t)*d i+
        Analytic.B x*(∑ t, g*d t)*(∑ t, g*q i t)+
        Analytic.B x*(∑ t, g*K i t*d t)-
        ∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) =
      g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i))+
        (1+m x+Analytic.B x*y)*(g*(∑ t, g*q i t)*d i)+
        (Analytic.B x*(∑ t, g*d t))*(g*(∑ t, g*q i t))+
        Analytic.B x*(∑ t, g^2*K i t*d t)-
        g*(∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) := by
    intro i
    have hk : g*(∑ t, g*K i t*d t)=∑ t, g^2*K i t*d t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    calc
      _ = g*((y-∑ t, g*q i t)*(d i+(1-pHat*s i)*N i))+
        (1+m x+Analytic.B x*y)*(g*(∑ t, g*q i t)*d i)+
        (Analytic.B x*(∑ t, g*d t))*(g*(∑ t, g*q i t))+
        Analytic.B x*(g*(∑ t, g*K i t*d t))-
        g*(∑ t, g*(1-q i t)*max (d t-(1+m x+Analytic.B x*y)*d i) 0) := by ring
      _ = _ := by rw [hk]
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end MetricKMedian.GeneratorAverage
end
end

end OAI
