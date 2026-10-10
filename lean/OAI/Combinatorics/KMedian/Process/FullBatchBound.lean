import Mathlib
import OAI.Combinatorics.KMedian.Process.FrozenBatchBound
import OAI.Combinatorics.KMedian.Process.PhaseBatchBound

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem expected_step_bound (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (q : E → ℝ) {h g φ : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hg : 0 ≤ g) (hp1 : 2*h*g ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq : ∀ e, 2*h*g ≤ q e ∧ q e ≤ (1+φ)*(2*h*g))
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (PhysicalBatchLaw.law Z C (2*h*g) q (by positivity) hp1 hq0 hq1).expect
      (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
        (nextCap D d bForce A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+g*(∑ e ∈ relevant D S, charge D x g b d S e))+
      R*(16*((relevant D S).card:ℝ)*(N:ℝ)*h^2*g^2+
        8*((relevant D S).card:ℝ)*φ*h*g+
        256*((univ : Finset (relevant D S)).offDiag.card:ℝ)*h^2*g^2+
        6*h^2+8*((relevant D S).card:ℝ)*h^2*g) := by
  let μ := PhysicalBatchLaw.law Z C (2*h*g) q (by positivity) hp1 hq0 hq1
  have hpQ : 2*h*g ≤ 4*h*g := by nlinarith only [mul_nonneg hh hg]
  have hqQ : ∀ e, q e ≤ 4*h*g := by
    intro e
    have he := mul_le_mul_of_nonneg_right hφ1 (show 0 ≤ 2*h*g by positivity)
    linarith only [he, (hq e).2]
  have hf := expected_frozen_bound D Z C (2*h*g) q (by positivity) hp1 hq0 hq1
    hφ0 (show 0 ≤ 4*h*g by positivity) hpQ hqQ hq hC hself d S hx0 hx1 hg hR
    hd0 hdR hy hb0 hbR hbf0 hbf hheavy
  have ht := expected_time_advance μ (nextAlive D x g d S) (nextCap D d bForce)
    d S hx0 hx1 hg hR hh (fun i _ => hd0 i) hdR hy (nextAlive_subset D x g d S)
  have hm : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ (4*h*g)/2 := by
    intro e _
    exact PhysicalBatchLaw.marginal_le Z C (2*h*g) q (by positivity) hp1 hq0 hq1 hself hpQ hqQ e
  have hc := change_probability_le D μ x g d S hm
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*h*R by positivity)
  change μ.expect _ ≤ _ at hf ⊢
  have he : (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
      (nextCap D d bForce A)-potential x g d S b)=
      (fun A => (potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-
        potential x g d S b)+
        (potential (x*Real.exp (-h)) g d (nextAlive D x g d S A) (nextCap D d bForce A)-
        potential x g d (nextAlive D x g d S A) (nextCap D d bForce A))) := by
    funext A
    ring
  rw [he, μ.expect_add]
  calc
    _ ≤ ((2*h*g)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(2*h*g)^2/2+φ*(2*h*g)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*(4*h*g)^2+
        (h*timeRate x (mass g S)*PhysicalPotential.cost g d S+6*h^2*R+
          4*h*R*(((relevant D S).card:ℝ)*((4*h*g)/2))) := by
      exact add_le_add hf (ht.trans (add_le_add_right hmul _))
    _ = _ := by ring

end MetricKMedian.FixedBatch
end
end

end OAI
