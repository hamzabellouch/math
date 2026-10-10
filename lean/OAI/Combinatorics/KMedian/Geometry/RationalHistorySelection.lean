import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSelect
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalHistoryCount
import OAI.Combinatorics.KMedian.Geometry.RationalParameterizedHistory

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}
local instance rationalHistorySelectionCopyOrder : LinearOrder (Copy (F := F) q.Δ) := copyOrder

def completedGood (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) (z : SparseHistories.History (State F q.Δ q.g q.β)) : Bool :=
  decide ((completed d R B hB q.g q.β z).Nonempty ∧
    ((completed d R B hB q.g q.β z).card:ℚ) ≤ q.g*A.card+q.allowance)

def selectCompleted (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) : Option (Finset F) :=
  (SparseSelect.choose (q.tree d₀ A) (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z))).map
      (completed d R B hB q.g q.β)

theorem selectCompleted_spec (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    ∃ O : Finset F, q.selectCompleted d₀ d R A B hB=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ mass (q.g:ℝ) A+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,
        PhysicalPotential.cost (q.g:ℝ)
          (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  let μ := q.tree d₀ A
  let good := fun a : Fin μ.length => mass (q.g:ℝ) μ.states[a.val].1.1 ≤
    mass (q.g:ℝ) A+(q.allowance:ℝ)
  have hfail : μ.realIndex.prob (fun a => ¬ good a) ≤ τ := by
    have hc := histories_count_tail d₀ location hd₀ q.g q.β q.probabilityQ q.φ q.taperAt
      q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A q.T
      q.gpos q.gle (by exact_mod_cast q.probabilityQ_pos) q.φpos q.φle q.βpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA (by
        simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.count)
    have he : (q.allowance:ℝ)=(q.T:ℝ)*(4/((q.g:ℝ)*(q.β:ℝ))) := by
      simp only [allowance,Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
    have hf : μ.realIndex.prob (fun a => ¬ good a) ≤
      (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/((q.probabilityQ:ℝ)*(q.φ:ℝ)^2*(q.g:ℝ))) := by
      convert hc using 1
      unfold FiniteLaw.prob SparseIntegerLaw.expectation
      apply congrArg μ.realIndex.expect
      funext a
      simp only [good,he,not_le]
      rfl
    exact hf.trans (by simpa only [probabilityQ,Rat.cast_mul,Rat.cast_ofNat] using q.failure)
  have hprob : 1-τ ≤ μ.realIndex.prob (fun a => q.completedGood d R A B hB μ.states[a.val]=true) := by
    have hc := μ.realIndex.prob_compl good
    have hp : 1-τ ≤ μ.realIndex.prob good := by linarith only [hc,hfail]
    apply hp.trans (μ.realIndex.prob_mono ?_)
    intro a ha
    have hs := histories_completion d₀ d location client hd₀ hd q.g q.β q.probabilityQ q.φ
      q.taperAt q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A B R hB
      q.T (fun t => Real.exp (-(t:ℝ)*(q.h:ℝ))) q.gpos q.unit
      (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA hBA hR hm hdR a
    simp only [completedGood,decide_eq_true_eq]
    refine ⟨hs.2.1 hj,?_⟩
    have hh := hs.1.trans ha
    dsimp only [mass] at hh
    exact_mod_cast hh
  obtain ⟨z,hz,hgood,hcost⟩ := SparseSelect.choose_bound μ (q.completedGood d R A B hB)
    (fun z => score d (completed d R B hB q.g q.β z)) (sub_pos.mpr hτ) hprob
    (fun z => score_nonneg d (fun c f => by exact_mod_cast (hd c f ▸ dist_nonneg)) _)
    (q.completed_expectation d₀ d location client hd₀ hd A B R hB hA hBA hR hm hdR hatt)
  have hgood' := of_decide_eq_true hgood
  refine ⟨completed d R B hB q.g q.β z,?_,hgood'.1,?_,?_⟩
  · change Option.map _ (SparseSelect.choose μ _ _)=_
    rw [hz]
    rfl
  · dsimp only [mass]
    exact_mod_cast hgood'.2
  · exact hcost.trans_eq (by ring)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
