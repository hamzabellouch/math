import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalGeometryScan
import OAI.Combinatorics.KMedian.Geometry.RationalAllParameters
import OAI.Combinatorics.KMedian.Geometry.RationalUnitInput

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

def suppliers : RationalSuppliers.Data f (U.representatives p.M).card :=
  RationalBundles.suppliers (fun t => U.F (U.ridx p.M t)) U.y
    (fun t => R.c (U.ridx p.M t)) R.i
    (fun t u => U.dd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => U.dc (U.ridx p.M t) a) (fun t => U.V (U.ridx p.M t)) p.M p.δ p.γ
    (fun t u => R.hdd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => R.hdc (U.ridx p.M t) a) U.hy p.hM p.hδ (by linarith only [p.hδ1])
    p.hθ p.hγ p.hγ1 (fun t => U.hu (U.ridx p.M t)) (fun _ => rfl)
    (U.representative_separation p.M p.hM.le)

def scan (B : ℚ) : Option (Finset (Fin f)) := (U.suppliers R p).scan p.round U.df U.dc B

theorem scan_spec (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j) (B : ℚ)
    (hB : (∑ a, (U.y a:ℝ))+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (B:ℝ)) :
    ∃ O : Finset (Fin f), U.scan R p B=some O ∧ O.Nonempty ∧ (O.card:ℝ)≤(B:ℝ) ∧
      (Completion.Rational.score U.dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(∑ c, (U.V c:ℝ)) := by
  classical
  choose rep hV hd using U.representative_cover p.M p.hM.le
  obtain ⟨O,hO,hOn,hOc,hCost⟩ := RationalBundles.scan_geometry p.round p.even hτ0 hτ hj
    (fun t => U.F (U.ridx p.M t)) U.F U.y (fun t => R.c (U.ridx p.M t)) R.i R.c
    (fun t u => U.dd (U.ridx p.M t) (U.ridx p.M u)) (fun t a => U.dc (U.ridx p.M t) a)
    U.df U.dc (fun t => U.V (U.ridx p.M t)) U.V rep p.M p.δ p.γ p.T₁ B
    (fun t u => R.hdd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => R.hdc (U.ridx p.M t) a) R.hdf R.hdc U.hy U.hy1
    p.hM p.hδ p.hδ1 p.hθ p.hγ p.hγ1 p.hT p.hα p.failure hB
    (fun t => U.hu (U.ridx p.M t)) (fun _ => rfl) U.hu (fun _ => rfl)
    (U.representative_separation p.M p.hM.le)
    (fun t => U.hnear (U.ridx p.M t)) hV
    (fun c => by rw [R.hdd]; exact_mod_cast hd c)
  refine ⟨O,hO,hOn,hOc,hCost.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun c _ => by exact_mod_cast U.V_nonneg c))
  apply mul_le_mul_of_nonneg_left p.error
  exact div_nonneg (by positivity) (by linarith only [hτ])

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
