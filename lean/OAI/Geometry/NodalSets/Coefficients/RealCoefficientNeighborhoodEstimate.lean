import OAI.Geometry.NodalSets.Elliptic.CompactParameterJetBounds
import OAI.Geometry.NodalSets.Elliptic.RealEllipticityNeighborhood
import OAI.Geometry.NodalSets.Elliptic.RealLocalBallJetEstimate

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Metric Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_coefficient_neighborhood_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hsO : closedBall y R ⊆ O)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V₀ : Yau.Jets.Coord → ℝ)
    (hC₀ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C₀ x i j)) (hV₀ : ContDiff ℝ ∞ V₀)
    (hp₀ : ∀ x ∈ closedBall y R, (C₀ x).PosDef) :
    ∃ eps > 0, ∃ K > 0,
      ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V W : Yau.Jets.Coord → ℝ),
        (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
        (∀ x i j, C x i j=C x j i) →
        (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
          (∀ i j, |partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x| ≤ eps) ∧
          |partialJet V es x-partialJet V₀ es x| ≤ eps) →
        (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
        IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
        IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
        (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
          K*(∫ x in closedBall y R, W x^2) := by
  have hQ := isCompact_closedBall y R
  obtain ⟨k,hk,L,hL,hellUnit⟩ := compact_parameter_matrix_ellipticity (T := Unit)
    (fun _ ↦ C₀) hQ
    (fun i j ↦ (hC₀ i j).continuous.comp (continuous_subtype_val.comp continuous_snd))
    (fun _ ↦ hp₀)
  have hell := hellUnit ()
  obtain ⟨BC,hBC,hCd⟩ := compact_parameter_finite_jet_bound (T := Unit) n
    (fun ij : Fin 4 × Fin 4 ↦ fun _ x ↦ C₀ x ij.1 ij.2) hQ
    (fun ij ds _ ↦ (partialJet_smooth _ (hC₀ ij.1 ij.2) ds).continuous.comp
      (continuous_subtype_val.comp continuous_snd))
  obtain ⟨BV,hBV,hVd⟩ := compact_parameter_finite_jet_bound (T := Unit) n
    (fun _ : Unit ↦ fun _ x ↦ V₀ x) hQ
    (fun _ ds _ ↦ (partialJet_smooth V₀ hV₀ ds).continuous.comp
      (continuous_subtype_val.comp continuous_snd))
  let eps := min (k/32) 1
  let B := BC+BV+1
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; linarith
  obtain ⟨K,hK,hest⟩ := real_local_ball_jet_estimate O hO n (k/2) (L+k/2) B B
    (by positivity) (by positivity) hB hB y r R hr hR hsO
  refine ⟨eps,heps,K,hK,fun C V W hC hV hW hs hclose he ↦ ?_⟩
  have hentry : ∀ x ∈ closedBall y R, ∀ i j, |C x i j-C₀ x i j| ≤ k/32 := by
    intro x hx i j
    exact ((hclose x hx [] (by simp)).1 i j).trans (min_le_left _ _)
  have hellC := real_ellipticity_neighborhood (closedBall y R) C₀ k L hk
    (fun x hx z ↦ (hell x hx z).1) (fun x hx z ↦ (hell x hx z).2) C hentry
  have hbounds : ∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
      (∀ i j, |partialJet (fun z ↦ C z i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B := by
    intro x hx es hes
    have hdelta := hclose x hx es hes
    constructor
    · intro i j
      have hbase := hCd (i,j) () x hx es hes
      have htri := abs_add_le (partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x)
        (partialJet (fun z ↦ C₀ z i j) es x)
      rw [sub_add_cancel] at htri
      have hsmall := (hdelta.1 i j).trans (min_le_right _ _)
      dsimp only [B]
      linarith
    · have hbase := hVd () () x hx es hes
      have htri := abs_add_le (partialJet V es x-partialJet V₀ es x) (partialJet V₀ es x)
      rw [sub_add_cancel] at htri
      have hsmall := hdelta.2.trans (min_le_right _ _)
      dsimp only [B]
      linarith
  exact hest C V W hC hV hW hs (fun x hx z ↦ (hellC x hx z).1)
    (fun x hx z ↦ (hellC x hx z).2) (fun x hx ↦ (hbounds x hx [] (by simp)).2) hbounds he

end
end Yau.Geometry

end OAI
