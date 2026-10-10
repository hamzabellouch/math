import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters
import OAI.Combinatorics.KMedian.Geometry.RationalImageCost
import OAI.Combinatorics.KMedian.Geometry.RationalGridRound

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

def countCandidates (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) : List (Finset H) :=
  ns.flatMap (fun n => ((q.roundCounts (fun a b => d₀ (orig a) (orig b))
    (fun c a => d c (orig a)) n).map (fun O => O.image orig)).toList)

def candidateGood (B : ℚ) (O : Finset H) : Bool := decide (O.Nonempty ∧ (O.card:ℚ) ≤ B)

def roundList (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) (B : ℚ) : Option (Finset H) :=
  SparseSelect.best (candidateGood B) (score d) (q.countCandidates d₀ d orig ns)

theorem candidate_mem (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) (n : F → ℕ) (hn : n∈ns) (O : Finset F)
    (hO : q.roundCounts (fun a b => d₀ (orig a) (orig b)) (fun c a => d c (orig a)) n=some O) :
    O.image orig∈q.countCandidates d₀ d orig ns := by
  apply List.mem_flatMap.mpr
  refine ⟨n,hn,?_⟩
  rw [hO]
  simp

theorem roundList_spec (hτ : τ<1) (hj : 0<j)
    (d₀ : H → H → ℚ) (d : Fin j → H → ℚ)
    (location : H → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (orig : F → H) (ns : List (F → ℕ)) (B : ℚ)
    (n : F → ℕ) (hn : n∈ns) (hcap : ∀ a, n a ≤ q.Δ)
    (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (hbudget : (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset H, q.roundList d₀ d orig ns B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c (orig a):ℝ)) := by
  obtain ⟨U,hU,hUn,hUc,hUcost⟩ := q.roundCounts_spec hτ hj
    (fun a b => d₀ (orig a) (orig b)) (fun c a => d c (orig a))
    (location ∘ orig) client (fun a b => hd₀ (orig a) (orig b)) (fun c a => hd c (orig a))
    n hcap hm r hr0 hr1 hrsum
  have hmem := q.candidate_mem d₀ d orig ns n hn U hU
  have hcard : ((U.image orig).card:ℝ) ≤ (B:ℝ) :=
    (Nat.cast_le.mpr card_image_le).trans (hUc.trans hbudget)
  have hGood : candidateGood B (U.image orig)=true := by
    apply decide_eq_true
    exact ⟨hUn.image orig,by exact_mod_cast hcard⟩
  obtain ⟨O,hO,_hOm,hOG,hOC⟩ := SparseSelect.best_of_witness (candidateGood B) (score d)
    (q.countCandidates d₀ d orig ns) (U.image orig) hmem hGood
  have hOG' := of_decide_eq_true hOG
  refine ⟨O,hO,hOG'.1,by exact_mod_cast hOG'.2,?_⟩
  have hC : (score d O:ℝ) ≤ (score (fun c a => d c (orig a)) U:ℝ) := by
    exact_mod_cast (hOC.trans_eq (score_image d orig U))
  exact hC.trans hUcost

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
