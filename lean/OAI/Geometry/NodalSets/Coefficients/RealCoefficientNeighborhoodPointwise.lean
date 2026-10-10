import OAI.Geometry.NodalSets.Coefficients.RealCoefficientNeighborhoodEstimate
import OAI.Geometry.NodalSets.Elliptic.RealCompactInteriorPointwise

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Metric Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_coefficient_neighborhood_pointwise (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hsO : closedBall y R ⊆ O)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V₀ : Yau.Jets.Coord → ℝ)
    (hC₀ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C₀ x i j)) (hV₀ : ContDiff ℝ ∞ V₀)
    (hp₀ : ∀ x ∈ closedBall y R, (C₀ x).PosDef) :
    ∃ eps > 0, ∃ K > 0,
      ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V W : Yau.Jets.Coord → ℝ),
        (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
        (∀ x i j, C x i j=C x j i) →
        (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n+5 →
          (∀ i j, |partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x| ≤ eps) ∧
          |partialJet V es x-partialJet V₀ es x| ≤ eps) →
        (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
        ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
          (partialJet W ds x)^2 ≤ K*(∫ z in closedBall y R, W z^2) := by
  let t := (r+R)/2
  have hrt : r < t := by dsimp [t]; linarith
  have htR : t < R := by dsimp [t]; linarith
  obtain ⟨eps,heps,L,hL,hest⟩ := real_coefficient_neighborhood_estimate O hO
    (n+5) y t R (hr.trans hrt) htR hsO C₀ V₀ hC₀ hV₀ hp₀
  have hinner : closedBall y r ⊆ interior (closedBall y t) :=
    (closedBall_subset_ball hrt).trans ball_subset_interior_closedBall
  obtain ⟨A,hA,ha⟩ := real_compact_interior_pointwise (isCompact_closedBall y r)
    (isCompact_closedBall y t) hinner n
  refine ⟨eps,heps,A*L,mul_pos hA hL,fun C V W hC hV hW hs hclose he ds hd x hx ↦ ?_⟩
  have hb := (hest C V W hC hV hW hs hclose he).2.2
  calc
    _ ≤ A*(∫ z in closedBall y t, realFiniteJetSquare W (n+5) z) := ha W hW ds hd x hx
    _ ≤ A*(L*(∫ z in closedBall y R, W z^2)) := mul_le_mul_of_nonneg_left hb hA.le
    _ = _ := by ring

end
end Yau.Geometry

end OAI
