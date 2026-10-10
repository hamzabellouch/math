import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalHistoryCompletion
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

def probabilityQ : ℚ := 2*q.h*q.g

theorem probabilityQ_pos : 0 < q.probabilityQ := by
  have hh := q.hpos
  have hg := q.gpos
  exact_mod_cast (show 0 < 2*(q.h:ℝ)*(q.g:ℝ) by positivity)

theorem probabilityQ_le : (1+q.φ)*q.probabilityQ ≤ 1 := by
  exact_mod_cast q.probability

def taperAt (t : ℕ) : ℚ := if ht : t<q.T then q.taper ⟨t,ht⟩ else 1/2

theorem taperAt_pos (t : ℕ) : 0 < (q.taperAt t:ℝ) := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_pos _
  · norm_num

theorem taperAt_le (t : ℕ) : (q.taperAt t:ℝ) ≤ 1/2 := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_le _
  · norm_num

theorem taperAt_error (t : ℕ) (ht : t<q.T) :
    |(q.taperAt t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*(q.h:ℝ)))| ≤ (q.ζ:ℝ) := by
  simpa only [taperAt,dite_eq_left ht] using q.taper_error ⟨t,ht⟩

def allowance : ℚ := (q.T:ℚ)*(4/(q.g*q.β))

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}
local instance rationalParameterizedHistoryCopyOrder : LinearOrder (Copy (F := F) q.Δ) := copyOrder

def tree (d₀ : F → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :=
  histories d₀ q.g q.β q.probabilityQ q.φ q.taperAt q.probabilityQ_pos.le
    (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T

theorem completed_expectation (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
      (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
        (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  have hE := histories_completed_expectation d₀ d location client hd₀ hd q.g q.β q.probabilityQ
    q.φ q.taperAt q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A B R hB
    q.T (by simp [probabilityQ]) q.gpos q.gle q.unit
    (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA q.hpos.le q.hle q.φle q.small
    q.survival q.ζpos.le q.ζle q.taperAt_error hBA hR hm hdR hatt
  apply hE.trans
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  let v := PhysicalPotential.cost (q.g:ℝ)
    (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)
  have hv : 0 ≤ v := cost_nonneg q.gpos.le (fun _ _ => dist_nonneg)
  have hr : (R c:ℝ) ≤ (q.Δ:ℝ)*v := by
    obtain ⟨i,hi,he⟩ := hatt c
    have hp := point_cost_le q.gpos.le (fun (i' : Copy (F := F) q.Δ) _ =>
      (dist_nonneg : 0 ≤ dist (client c) (location i'.1))) hi
    rw [hd,← he] at hp
    have hmul := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ q.Δ by positivity)
    have hu : (q.Δ:ℝ)*(q.g:ℝ)=1 := by rw [mul_comm]; exact q.unit
    simpa only [← mul_assoc,hu,one_mul] using hmul
  have hdec := FiniteLaw.decay_exp (show (q.h:ℝ) ≤ 2 by linarith only [q.hle]) q.T
  have hpow := mul_le_mul_of_nonneg_left hdec
    (show 0 ≤ 5*(R c:ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ) ≤ 5) (hR c))
  have hrad := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 5*Real.exp (-(q.T:ℝ)*(q.h:ℝ)/2) by positivity)
  have hC : 0 ≤ batchConstant q.Δ := by unfold batchConstant; positivity
  have hh := q.hpos.le
  have hφ := q.φpos.le
  have hbatch := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (q.T:ℝ)*batchConstant q.Δ*(q.h:ℝ)*((q.φ:ℝ)+(q.h:ℝ)) by positivity)
  have herr := mul_le_mul_of_nonneg_right q.error hv
  change (1+2/Real.exp 1)*v+(q.T:ℝ)*((q.h:ℝ)*((q.g:ℝ)+12*(q.ζ:ℝ))*v+
    batchConstant q.Δ*(q.h:ℝ)*((q.φ:ℝ)+(q.h:ℝ))*(R c:ℝ))+
      5*(R c:ℝ)*(1-(q.h:ℝ)/2)^q.T ≤ (1+2/Real.exp 1+τ)*v
  nlinarith only [hpow,hrad,hbatch,herr]

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
