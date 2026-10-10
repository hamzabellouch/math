import OAI.Geometry.NodalSets.Elliptic.RealCompatibleBallLimits

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_local_jet_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ g : List (Fin 4) → Yau.Jets.Coord → ℝ, (∀ ds, Continuous (g ds)) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (g ds) atTop Q := by
  obtain ⟨f,_,nu,hnu,ht⟩ := real_jet_ball_subsequence W hW hb
  have hh (ds : List (Fin 4)) := real_compatible_ball_limits
    (fun j ↦ partialJet (W (nu j)) ds) (fun j ↦ (partialJet_smooth _ (hW _) ds).continuous)
    (fun R ↦ f R ds) (fun R ↦ ht R ds)
  choose g hg hconv using hh
  exact ⟨g,hg,nu,hnu,hconv⟩

end
end Yau.Geometry

end OAI
