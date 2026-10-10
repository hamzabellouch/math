import OAI.Geometry.NodalSets.Charts.RealFiniteAtlasBallSubsequence
import OAI.Geometry.NodalSets.Charts.SphereFiniteOrderLimitGluing

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_jet_compactness (P : Finset Base) (s r : ℝ) (hsr : s < r) (n : ℕ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) s,
      sphereChartCoordMap p z=x)
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (B : {p // p ∈ P} → ℝ) (hB : ∀ p, 0 ≤ B p)
    (hb : ∀ (p : {p // p ∈ P}) j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r,
        |partialJet (w j ∘ sphereChartCoordMap p.val) ds x| ≤ B p) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        ∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 r) := by
  classical
  obtain ⟨nu,hnu,hlim⟩ := real_finite_atlas_ball_subsequence
    (fun (p : {p // p ∈ P}) j ↦ w j ∘ sphereChartCoordMap p.val)
    (fun p j ↦ ((hw j).comp (sphereChartCoordMap_smooth p.val)).contDiff) r n B hB hb
  choose f hfc hfs hft hfj using hlim
  obtain ⟨v,hv,ht,hvchart⟩ := sphere_finite_order_limit_gluing P r n (by
    intro x
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨p,hp,z,ball_subset_ball hsr.le hz,he⟩) (fun j ↦ w (nu j)) f hfs hft
  refine ⟨v,hv,nu,hnu,ht,?_⟩
  intro p hp ds hd
  apply (hfj ⟨p,hp⟩ ds hd).congr_right
  intro x hx
  exact (partialJet_germ_eq (v ∘ sphereChartCoordMap p) (f ⟨p,hp⟩) x
    (Filter.Eventually.mono (isOpen_ball.mem_nhds hx) (fun y hy ↦ hvchart ⟨p,hp⟩ hy)) ds).symm

end
end Yau.Target

end OAI
