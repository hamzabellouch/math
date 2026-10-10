import OAI.Geometry.NodalSets.Elliptic.RealCutoffBallIntegrals

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section

theorem real_ball_jet_estimate (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ closedBall y R, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ closedBall y R, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ closedBall y R, |V x| ≤ M) →
      (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun z ↦ C z i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
      IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
      (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
        K*(∫ x in closedBall y R, W x^2) := by
  obtain ⟨eta,heta,hc,hval,hsupport,hone,hnest⟩ := real_ball_cutoff_chain y r R hr hR
  obtain ⟨K,hK,hest⟩ := real_interior_jet_estimate n k L M B hk hL hM hB eta heta hc hnest
  refine ⟨K,hK,?_⟩
  intro C V W hC hV hW hs hlo hhi hpot hb he
  obtain ⟨_,_,hbound⟩ := hest C V W hC hV hW hs
    (fun x hx ↦ hlo x (hsupport 0 hx)) (fun x hx ↦ hhi x (hsupport 0 hx))
    (fun x hx ↦ hpot x (hsupport 0 hx)) (fun x hx ↦ hb x (hsupport 0 hx)) he
  have hinner := real_cutoff_inner_integral_le (eta n) _ (heta n) (hc n)
    (realFiniteJetSquare_smooth W hW n).continuous (realFiniteJetSquare_nonneg W n) y r (hone n)
  have houter := real_cutoff_outer_integral_le (eta 0) (fun x ↦ W x^2) (heta 0) (hc 0)
    (hW.pow 2).continuous (fun x ↦ sq_nonneg _) (hval 0) y R (hsupport 0)
  exact ⟨(realFiniteJetSquare_smooth W hW n).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall y r),
    (hW.pow 2).continuous.continuousOn.integrableOn_compact (isCompact_closedBall y R),
    hinner.trans (hbound.trans (mul_le_mul_of_nonneg_left houter hK.le))⟩

end
end Yau.Geometry

end OAI
