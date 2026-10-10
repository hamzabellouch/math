import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalFractionalScan
import OAI.Combinatorics.KMedian.Geometry.RationalIndexedCost

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def clientDistance (I : Instance) (c c' : Fin I.clients.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl c) (I.clients.orderEmbOfFin rfl c')

 def facilityDistance (I : Instance) (b b' : Fin I.facilities.card) : ℚ :=
  I.distance (I.facilities.orderEmbOfFin rfl b) (I.facilities.orderEmbOfFin rfl b')

 theorem clientDistance_self (I : Instance) (c : Fin I.clients.card) : I.clientDistance c c=0 :=
  (I.distance_eq_zero _ _).mpr rfl

 theorem clientDistance_comm (I : Instance) (c c' : Fin I.clients.card) :
    I.clientDistance c c'=I.clientDistance c' c := I.distance_symm _ _

 def fractionalRound (I : Instance) (a : TruncatedLP.FractionalData I.facilities.card I.clients.card)
    (ha : a.Valid I.k) (hj : I.clients.Nonempty) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) :
    Option (Finset (Fin I.n)) :=
  letI := I.pseudoMetric
  (FractionalRefinement.scan a I.k ha (card_pos.mpr hj) I.indexedDistance I.clientDistance I.facilityDistance
    I.indexedDistance_nonneg I.clientDistance_self I.clientDistance_comm
    (I.facilities.orderEmbOfFin rfl) (I.clients.orderEmbOfFin rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p (I.k+C)).map
    (fun O => O.image (I.facilities.orderEmbOfFin rfl))

 theorem fractionalRound_spec (I : Instance) (a : TruncatedLP.FractionalData I.facilities.card I.clients.card)
    (ha : a.Valid I.k) (hj : I.clients.Nonempty) {η τ : ℝ} (p : RationalAllParameters η τ)
    (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin I.n), I.fractionalRound a ha hj p C=some O ∧
      O⊆I.facilities ∧ O.Nonempty ∧ O.card≤I.k+C ∧
       cost I O≤((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value I.indexedDistance:ℝ) := by
  let := I.pseudoMetric
  obtain ⟨O,hO,hOn,hOc,hCost⟩ := FractionalRefinement.scan_spec a I.k ha (card_pos.mpr hj)
    I.indexedDistance I.clientDistance I.facilityDistance I.indexedDistance_nonneg
    I.clientDistance_self I.clientDistance_comm (I.facilities.orderEmbOfFin rfl) (I.clients.orderEmbOfFin rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p hη hτ0 hτ C hC
  refine ⟨O.image (I.facilities.orderEmbOfFin rfl),?_,?_,hOn.image _,card_image_le.trans hOc,?_⟩
  · unfold fractionalRound
    rw [hO]
    rfl
  · intro b hb
    obtain ⟨u,_,rfl⟩ := mem_image.mp hb
    exact I.facilities.orderEmbOfFin_mem rfl u
  · rw [I.indexed_score_image, I.cast_rationalCost] at hCost
    exact hCost

end MetricKMedian.Instance
end

end OAI
