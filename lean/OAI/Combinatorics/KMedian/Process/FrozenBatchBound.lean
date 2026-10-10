import Mathlib
import OAI.Combinatorics.KMedian.Geometry.PotentialBounds
import OAI.Combinatorics.KMedian.Process.BatchEstimate
import OAI.Combinatorics.KMedian.Geometry.FixedBatchTransition

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

omit [Fintype E] in
 theorem charge_bound (D : Actions I E) {x g R b : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (e : E) :
    |charge D x g b d S e| ≤ 8*R := by
  unfold charge
  split_ifs with he
  · exact internal_charge_bound hx0 hx1 hg hR (fun i _ => hd0 i) hdR hy hb0 hbR
      sdiff_subset (hd0 _) (hdR _ he.2)
  · apply external_charge_bound hx0 hx1 (mass_nonneg hg S) hy hR
      (mass_nonneg hg _) ((mass_mono hg inter_subset_left).trans hy)
      (cost_nonneg hg (fun i _ => hd0 i)) (cost_mono hg (fun i _ => hd0 i) inter_subset_left)
      (cost_le_radius hg hR hdR hy) (le_min hb0 (hd0 _))
      ((min_le_left _ _).trans hbR)

 theorem frozen_change_bound (D : Actions I E) {x g R b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤ 8*R := by
  have hsub := nextAlive_subset D x g d S A
  have hnew := potential_bounds hx0 hx1 hg hR (fun i _ => hd0 i)
    (fun i hi => hdR i (hsub hi)) ((mass_mono hg hsub).trans hy)
    (nextCap_nonneg D d A hbf0 (fun e _ => hd0 _))
    ((nextCap_le_force D d bForce A).trans (hbf.trans hbR))
  have hold := potential_bounds hx0 hx1 hg hR (fun i _ => hd0 i) hdR hy hb0 hbR
  linarith only [hnew.2, hold.1]

theorem expected_frozen_bound (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
    (hpQ : p ≤ Q) (hqQ : ∀ e, q e ≤ Q)
    (hq : ∀ e, p ≤ q e ∧ q e ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (PhysicalBatchLaw.law Z C p q hp0 hp1 hq0 hq1).expect
      (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
      (p/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*p^2/2+φ*p/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2 := by
  apply PhysicalBatchLaw.relevant_generator_estimate Z (relevant D S) C p q
    (charge D x g b d S) hp0 hp1 hq0 hq1 hφ (by positivity) hQ hpQ hqQ hq hC hself
  · exact fun e _ => charge_bound D d S hx0 hx1 hg hR hd0 hdR hy hb0 hbR e
  · exact fun A => frozen_change_bound D d S A hx0 hx1 hg hR hd0 hdR hy hb0 hbR hbf0 hbf
  · exact fun A ha => frozen_zero D d S A hy hbf ha
  · exact fun A e ha => frozen_one D d S A e hg (fun i _ => hd0 i) hy hbf hheavy ha

end MetricKMedian.FixedBatch
end
end

end OAI
