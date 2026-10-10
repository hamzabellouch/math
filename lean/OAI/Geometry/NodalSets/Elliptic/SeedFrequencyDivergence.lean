import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Real
import OAI.Geometry.NodalSets.Elliptic.SphericalSeed

namespace OAI

namespace Yau.Target
open Filter Manifold
open scoped Topology ContDiff ENNReal
noncomputable section

lemma seedEigenvalue_window_separation {n m : ℕ} (h : 2*n+1 ≤ m) :
    4*seedEigenvalue n < seedEigenvalue m := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hh : 2*(n:ℝ)+1 ≤ m := by exact_mod_cast h
  have hs := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 2*n+1) hh
  unfold seedEigenvalue
  nlinarith

lemma seed_window_eigenvalues_tendsto (N : ℕ → ℕ) (mu : ℕ → ℝ)
    (hN : ∀ k, k+1 ≤ N k) (hmu : ∀ k, seedEigenvalue (N k)/2 ≤ mu k) :
    Tendsto mu atTop atTop := by
  apply tendsto_atTop_mono (fun k ↦ ?_) (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k:ℝ)) atTop atTop)
  have hk : (k:ℝ)+1 ≤ N k := by exact_mod_cast hN k
  have hn : (0:ℝ) ≤ N k := Nat.cast_nonneg _
  have hh := hmu k
  unfold seedEigenvalue at hh
  nlinarith [sq_nonneg (N k:ℝ)]

theorem mainTarget_of_seed_windows (g : SmoothMetric) (N : ℕ → ℕ)
    (mu : ℕ → ℝ) (u : ℕ → Manifold5 → ℝ)
    (hN : ∀ k, k+1 ≤ N k)
    (hmu : ∀ k, 0 < mu k) (hwindow : ∀ k, seedEigenvalue (N k)/2 ≤ mu k)
    (hu0 : ∀ k, u k ≠ 0) (hu : ∀ k, ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (u k))
    (he : ∀ k x, -chartLaplacian g (extChartAt modelWithCorners x) (u k) (extChartAt modelWithCorners x x) =
      mu k*u k x)
    (hratio : ∀ k : ℕ, ENNReal.ofReal ((k:ℝ)+1) < nodalMeasure g (u k)/ENNReal.ofReal (Real.sqrt (mu k))) :
    MainTarget := by
  refine ⟨g,mu,u,hmu,hu0,hu,he,seed_window_eigenvalues_tendsto N mu hN hwindow,?_⟩
  apply tendsto_nhds_top_mono' ?_ (fun k ↦ (hratio k).le)
  apply ENNReal.tendsto_ofReal_atTop.comp
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end
end Yau.Target

end OAI
