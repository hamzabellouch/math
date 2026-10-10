import Mathlib.Topology.UniformSpace.UniformApproximation
import OAI.Geometry.NodalSets.Elliptic.RealFiniteBallJetSubsequenceLemmas
import OAI.Geometry.NodalSets.Elliptic.RealFiniteLocalJetLimit

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_finite_ball_limit_identification (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (f : {ds : List (Fin 4) // ds.length ≤ n} → closedBall y r → ℝ)
    (ht : ∀ ds : {ds : List (Fin 4) // ds.length ≤ n},
      TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W j) ds.val x) (f ds) atTop) :
    ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall y r) ∧
      ContDiffOn ℝ n v (ball y r) ∧
      TendstoUniformlyOn W v atTop (closedBall y r) ∧
      ∀ ds : List (Fin 4), ds.length ≤ n →
        TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop (ball y r) := by
  classical
  let g (ds : List (Fin 4)) (x : Yau.Jets.Coord) :=
    if hd : ds.length ≤ n then if hx : x ∈ closedBall y r then f ⟨ds,hd⟩ ⟨x,hx⟩ else 0 else 0
  have hu (ds : List (Fin 4)) (hd : ds.length ≤ n) :
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop (closedBall y r) := by
    rw [tendstoUniformlyOn_iff_restrict]
    change TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W j) ds x)
      (fun x : closedBall y r ↦ g ds x) atTop
    have heq : (fun x : closedBall y r ↦ g ds x) = f ⟨ds,hd⟩ := by
      funext x
      simp only [g,dite_eq_left hd,dite_eq_left x.property]
    rw [heq]
    exact ht ⟨ds,hd⟩
  have hc (ds : List (Fin 4)) (hd : ds.length ≤ n) : ContinuousOn (g ds) (closedBall y r) :=
    (hu ds hd).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun j ↦ (partialJet_smooth (W j) (hW j) ds).continuous.continuousOn)))
  have hd (ds : List (Fin 4)) (hh : ds.length < n) (x : Yau.Jets.Coord) (hx : x ∈ ball y r) :
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x :=
    real_finite_local_jet_limit_derivative (ball y r) isOpen_ball W hW n g
      (fun es he ↦ (hu es he).mono ball_subset_closedBall) ds hh x hx
  refine ⟨g [],hc [] (by simp),real_finite_local_jet_limit_contDiffOn (ball y r) isOpen_ball n g
    (fun es he ↦ (hc es he).mono ball_subset_closedBall) hd,hu [] (by simp),?_⟩
  intro ds hh
  apply ((hu ds hh).mono ball_subset_closedBall).congr_right
  exact (real_finite_local_jet_limit_identification (ball y r) isOpen_ball n g hd ds hh).symm

theorem real_finite_ball_smooth_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall y r, |partialJet (W j) ds x| ≤ B) :
    ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall y r) ∧ ContDiffOn ℝ n v (ball y r) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformlyOn (fun j ↦ W (nu j)) v atTop (closedBall y r) ∧
        ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop (ball y r) := by
  obtain ⟨f,hf,nu,hnu,ht⟩ := real_finite_ball_jet_subsequence W hW y r n B hB hb
  obtain ⟨v,hv,hs,hzero,hjet⟩ := real_finite_ball_limit_identification
    (fun j ↦ W (nu j)) (fun j ↦ hW (nu j)) y r n f ht
  exact ⟨v,hv,hs,nu,hnu,hzero,hjet⟩

end
end Yau.Geometry

end OAI
