import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalImageCost
import OAI.Combinatorics.KMedian.Geometry.RationalAllParameters
import OAI.Combinatorics.KMedian.Geometry.RationalFractionalInput
import OAI.Combinatorics.KMedian.Geometry.RationalUnitScan

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

def scan (B : ℚ) : Option (Finset (Fin f)) :=
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  (U.scan R p B).map (fun O => O.image (original a k ha hj dc))

theorem scan_spec (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
      O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
        ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ) := by
  classical
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  have hm : (∑ b, (U.y b:ℝ))≤(k:ℝ)+1 := by
    exact_mod_cast input_mass a k ha hj dc dd df hdc hdd hds
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := U.scan_spec R p hτ0 hτ hj ((k:ℚ)+C) (by
    push_cast
    linarith only [hm,hC])
  refine ⟨O.image (original a k ha hj dc),?_,hOn.image _,?_,?_⟩
  · change (U.scan R p ((k:ℚ)+C)).map (fun O => O.image (original a k ha hj dc))=_
    rw [hO]
    rfl
  · have hOk : O.card≤k+C := by exact_mod_cast hOc
    exact (card_image_le).trans hOk
  · rw [Completion.Rational.score_image]
    change (Completion.Rational.score U.dc O:ℝ)≤_
    exact hOs.trans (mul_le_mul_of_nonneg_left
      (show (∑ c, (U.V c:ℝ))≤(a.value dc:ℝ) by
        exact_mod_cast input_cost a k ha hj dc dd df hdc hdd hds)
      (mul_nonneg (div_nonneg (by positivity) (by linarith only [hτ])) (by linarith only [hη])))

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
