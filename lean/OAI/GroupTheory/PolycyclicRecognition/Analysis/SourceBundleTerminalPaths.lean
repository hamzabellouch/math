import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceBundleBlockPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteSupportChainPaths

namespace OAI

/-! # A single source terminal path through the successful bundle boundaries -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G W : Type*} [Group N] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- All source bundle boundaries have the same height. Their common
template therefore survives concatenation without a sum of templates. -/
theorem exists_source_bundle_terminal_path
    (ι : N →* G) (π : G →* Multiplicative W) (hN : ∀ n, π (ι n) = 1)
    {h : ℕ} (initial : N) (φ : Fin h → N ≃* N) (products : Fin h → N)
    (x d : G) (E : Set W) (hE0 : (0 : W) ∈ E)
    (r L κ B : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (path : ∀ j : Fin h,
      Path (x * ι (sourceBundleBoundary initial φ products j.val) * d)
        (x * ι (sourceBundleBoundary initial φ products (j.val + 1)) * d))
    (hmetric : ∀ j, PathMetricBound (path j) L κ)
    (hheight : ∀ j t, ∃ w ∈ E,
      ‖(π (path j t)).toAdd -
          (π (x * ι (sourceBundleBoundary initial φ products j.val) * d)).toAdd -
        r • w‖ ≤ B) :
    ∃ γ : Path (1 : G)
        ((x * ι initial * d)⁻¹ * (x * ι (sourceBundleBoundary initial φ products h) * d)),
      PathMetricBound γ (L * 2 ^ h) (κ * 2 ^ h) ∧
      ∀ t, ∃ w ∈ E, ‖(π (γ t)).toAdd - r • w‖ ≤ B := by
  let vertex := fun j : Fin (h + 1) => x * ι (sourceBundleBoundary initial φ products j.val) * d
  let region := {g : G | ∃ w ∈ E, ‖(π g).toAdd - (π (vertex 0)).toAdd - r • w‖ ≤ B}
  have hv (j : Fin (h + 1)) : π (vertex j) = π (vertex 0) := by
    simp only [vertex, map_mul, hN, mul_one]
  have hedge (j : Fin h) : ∀ t, path j t ∈ region := by
    intro t
    obtain ⟨w, hw, he⟩ := hheight j t
    refine ⟨w, hw, ?_⟩
    rwa [show π (x * ι (sourceBundleBoundary initial φ products j.val) * d) =
      π (vertex 0) from hv j.castSucc] at he
  have hzero : vertex 0 ∈ region := by
    refine ⟨0, hE0, ?_⟩
    simpa only [sub_self, smul_zero, sub_zero, norm_zero] using hB
  obtain ⟨p, hp, hregion⟩ := exists_finite_chain_path L κ hL hκ region h vertex path hzero
    hmetric hedge
  let centered := centeredImagePath (id : G → G) continuous_id p
  have hm : PathMetricBound centered (L * 2 ^ h) (κ * 2 ^ h) := by
    simpa only [NNReal.coe_one, one_mul] using
      centeredImagePath_metric_bound (id : G → G) LipschitzWith.id p hp
  have hend : (x * ι initial * d)⁻¹ * (x * ι (sourceBundleBoundary initial φ products h) * d) =
      (vertex 0)⁻¹ * vertex (Fin.last h) := by
    simp only [vertex, Fin.val_zero, Fin.val_last, sourceBundleBoundary_zero]
  refine ⟨centered.cast rfl hend, hm, ?_⟩
  intro t
  obtain ⟨w, hw, he⟩ := hregion t
  refine ⟨w, hw, ?_⟩
  change ‖(π ((vertex 0)⁻¹ * p t)).toAdd - r • w‖ ≤ B
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

end PolycyclicRecognition

end

end OAI
