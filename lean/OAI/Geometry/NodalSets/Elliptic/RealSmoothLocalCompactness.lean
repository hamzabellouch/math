import OAI.Geometry.NodalSets.Elliptic.RealJetLimitDerivative
import OAI.Geometry.NodalSets.Elliptic.RealJetUniformDerivative
import OAI.Geometry.NodalSets.Elliptic.RealLocalJetLimits

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_smooth_local_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W (nu j)))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  obtain ⟨g,hg,nu,hnu,ht⟩ := real_local_jet_limits W hW hb
  have hd := real_jet_limit_hasFDerivAt (fun j ↦ W (nu j)) (fun j ↦ hW (nu j)) g ht
  have hs := real_jet_limit_smooth g hg hd
  have hi := real_jet_limit_identification g hd
  have hu (ds : List (Fin 4)) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
      TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet (g []) ds) atTop Q := by
    rw [hi ds]
    exact ht ds Q hQ
  refine ⟨g [],hs [],nu,hnu,hu,?_⟩
  intro n Q hQ
  exact real_uniform_iteratedFDeriv (fun j ↦ W (nu j)) (g []) (fun j ↦ hW (nu j)) (hs []) n Q
    (fun ds _ ↦ hu ds Q hQ)

end
end Yau.Geometry

end OAI
