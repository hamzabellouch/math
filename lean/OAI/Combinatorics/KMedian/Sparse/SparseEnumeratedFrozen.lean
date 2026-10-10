import Mathlib
import OAI.Combinatorics.KMedian.Process.FrozenBatchBound
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedEstimate

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I E : Type} [DecidableEq I] [DecidableEq E] [Fintype E] {n : ℕ}

theorem expected_frozen_bound (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
      ((p:ℝ)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2 := by
  apply SparseEnumeratedBatch.relevant_generator_estimate enum Z (relevant D S) C p q
    (charge D x g b d S) hp hq0 hφ (by positivity) hQ hpQ hqQ hq hC hself
  · exact fun e _ => charge_bound D d S hx0 hx1 hg hR hd0 hdR hy hb0 hbR e
  · exact fun A => frozen_change_bound D d S A hx0 hx1 hg hR hd0 hdR hy hb0 hbR hbf0 hbf
  · exact fun A ha => frozen_zero D d S A hy hbf ha
  · exact fun A e ha => frozen_one D d S A e hg (fun i _ => hd0 i) hy hbf hheavy ha

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
