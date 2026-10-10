import OAI.Geometry.NodalSets.Elliptic.CompactFamilyBallJetEstimate
import OAI.Geometry.NodalSets.Elliptic.RealTranslatedJetEmbedding

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_family_pointwise_estimate (n : ℕ)
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (y : Yau.Jets.Coord) (r : ℝ) (hr : 0 ≤ r)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i)
    (hp : ∀ t x, x ∈ closedBall y (r+2) → (C t x).PosDef)
    (hCjoint : ∀ i j ds, ds.length ≤ n+4 → Continuous (fun z : T × closedBall y (r+2) ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, ds.length ≤ n+4 → Continuous (fun z : T × closedBall y (r+2) ↦
      partialJet (V z.1) ds z.2)) :
    ∃ K > 0, ∀ t (W : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ W →
      (∀ x, Yau.coordDiv (realMatrixFlux (C t) W) x+V t x*W x=0) →
      ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
        (partialJet W ds x)^2 ≤ K*(∫ z in closedBall y (r+2), W z^2) := by
  obtain ⟨K,hK,hest⟩ := compact_family_ball_jet_estimate (n+4) C V y (r+1) (r+2)
    (by linarith) (by linarith) hC hV hs hp hCjoint hVjoint
  refine ⟨256*K,by positivity,?_⟩
  intro t W hW he ds hd x hx
  exact (real_uniform_jet_l2_embedding W hW n y r ds hd x hx).trans
    ((mul_le_mul_of_nonneg_left (hest t W hW he).2.2 (by norm_num : (0:ℝ) ≤ 256)).trans_eq (by ring))

end
end Yau.Geometry

end OAI
