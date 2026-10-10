import OAI.Geometry.NodalSets.Elliptic.FiniteSubsequenceSelection
import OAI.Geometry.NodalSets.SmoothLimit.RealFiniteBallSmoothLimit

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_finite_atlas_ball_subsequence {I : Type*} [Fintype I]
    (W : I → ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ i j, ContDiff ℝ ∞ (W i j)) (r : ℝ) (n : ℕ)
    (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hb : ∀ i j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r, |partialJet (W i j) ds x| ≤ B i) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i,
      ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall 0 r) ∧
        ContDiffOn ℝ n v (ball 0 r) ∧
        TendstoUniformlyOn (fun j ↦ W i (nu j)) v atTop (closedBall 0 r) ∧
        ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (W i (nu j)) ds)
            (partialJet v ds) atTop (ball 0 r) := by
  classical
  obtain ⟨nu,hnu,hR⟩ := finite_subsequence_selection (Finset.univ : Finset I)
    (fun i nu ↦ ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall 0 r) ∧
      ContDiffOn ℝ n v (ball 0 r) ∧
      TendstoUniformlyOn (fun j ↦ W i (nu j)) v atTop (closedBall 0 r) ∧
      ∀ ds : List (Fin 4), ds.length ≤ n →
        TendstoUniformlyOn (fun j ↦ partialJet (W i (nu j)) ds)
          (partialJet v ds) atTop (ball 0 r)) (by
      intro i nu hnu
      obtain ⟨v,hv,hs,mu,hmu,ht,hjet⟩ := real_finite_ball_smooth_subsequence
        (fun j ↦ W i (nu j)) (fun j ↦ hW i (nu j)) 0 r n (B i) (hB i)
        (fun j ↦ hb i (nu j))
      exact ⟨mu,hmu,v,hv,hs,ht,hjet⟩) (by
      intro i nu mu hR hmu
      obtain ⟨v,hv,hs,ht,hjet⟩ := hR
      exact ⟨v,hv,hs,ht.seq_tendstoUniformlyOn mu hmu.tendsto_atTop,
        fun ds hd ↦ (hjet ds hd).seq_tendstoUniformlyOn mu hmu.tendsto_atTop⟩)
  exact ⟨nu,hnu,fun i ↦ hR i (Finset.mem_univ i)⟩

end
end Yau.Geometry

end OAI
