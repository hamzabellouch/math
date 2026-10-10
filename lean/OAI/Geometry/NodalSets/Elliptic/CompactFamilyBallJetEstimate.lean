import OAI.Geometry.NodalSets.Elliptic.CompactParameterJetBounds
import OAI.Geometry.NodalSets.Elliptic.RealBallJetEstimate

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_family_ball_jet_estimate (n : ℕ)
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i)
    (hp : ∀ t x, x ∈ closedBall y R → (C t x).PosDef)
    (hCjoint : ∀ i j ds, ds.length ≤ n → Continuous (fun z : T × closedBall y R ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, ds.length ≤ n → Continuous (fun z : T × closedBall y R ↦
      partialJet (V z.1) ds z.2)) :
    ∃ K > 0, ∀ t (W : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ W →
      (∀ x, Yau.coordDiv (realMatrixFlux (C t) W) x+V t x*W x=0) →
      IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
      IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
      (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
        K*(∫ x in closedBall y R, W x^2) := by
  obtain ⟨k,hk,L,hL,hell⟩ := compact_parameter_matrix_ellipticity C (isCompact_closedBall y R)
    (fun i j ↦ hCjoint i j [] (by simp)) hp
  obtain ⟨M,hM,hpot⟩ := compact_parameter_scalar_bound V (isCompact_closedBall y R) (hVjoint [] (by simp))
  obtain ⟨BC,hBC,hCd⟩ := compact_parameter_finite_jet_bound n
    (fun ij : Fin 4 × Fin 4 ↦ fun t x ↦ C t x ij.1 ij.2) (isCompact_closedBall y R)
    (fun ij ↦ hCjoint ij.1 ij.2)
  obtain ⟨BV,hBV,hVd⟩ := compact_parameter_finite_jet_bound n
    (fun _ : Unit ↦ V) (isCompact_closedBall y R) (fun _ ↦ hVjoint)
  obtain ⟨K,hK,hest⟩ := real_ball_jet_estimate n k L M (BC+BV) hk hL hM.le
    (by positivity) y r R hr hR
  refine ⟨K,hK,?_⟩
  intro t W hW he
  apply hest (C t) (V t) W (hC t) (hV t) hW (hs t)
    (fun x hx z ↦ (hell t x hx z).1) (fun x hx z ↦ (hell t x hx z).2) (hpot t) _ he
  intro x hx ds hd
  exact ⟨fun i j ↦ (hCd (i,j) t x hx ds hd).trans (by linarith),
    (hVd () t x hx ds hd).trans (by linarith)⟩

end
end Yau.Geometry

end OAI
