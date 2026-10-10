import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteSupportChainPaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileChainHeightBounds

namespace OAI

/-! # The selected affine profiles control the whole image path -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

/-- Uniform approximation by one affine profile controls the actual
outward legs, short switches and return legs. The affine offset cancels
when the image path is centered at its original endpoint. -/
theorem exists_affine_profile_controlled_path
    {G W V Z : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [AddCommGroup V] [Module ℝ V]
    {N : ℕ} (x : G) (vertex : Fin (N + 1) → G)
    (φ : Z → G) (q : Z → V) (z₀ : Z)
    (d f : Fin N → ℝ → G) (hd : ∀ j, Continuous (d j)) (hd₀ : ∀ j, d j 0 = 1)
    (hf : ∀ j, Continuous (f j)) (hf₀ : ∀ j, f j 0 = 1)
    (b : Fin N → ℝ) (hstep : ∀ j, vertex j.succ = vertex j.castSucc * f j (b j))
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (A : V →ₗ[ℝ] W) (offset : W) (r ε L κ δ : ℝ)
    (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (Q : Set Z) (hz₀ : z₀ ∈ Q)
    (hgood : ∀ i z, z ∈ Q →
      ‖rescaledMapProfile J x (vertex i) r φ z - (A (q z) + offset)‖ ≤ ε)
    (E : Set V) (hE0 : (0 : V) ∈ E)
    (leg : Fin N → unitInterval → Z)
    (hleg : ∀ j t, leg j t ∈ Q)
    (hlegφ : ∀ j t, φ (leg j t) = φ z₀ * d j (Real.exp r * (t : ℝ)))
    (hlegE : ∀ j t, q (leg j t) - q z₀ ∈ E)
    (hmetric : ∀ j, PathMetricBound
      (supportVisitPath (d j) (hd j) (hd₀ j) (f j) (hf j) (hf₀ j)
        (x * vertex j.castSucc) (φ z₀) (Real.exp r) (b j)) L κ)
    (hswitch : ∀ j t, dist
      ((x * vertex j.castSucc) * f j ((t : unitInterval) * b j) *
        (φ z₀ * d j (Real.exp r)))
      (((x * vertex j.castSucc) * φ z₀) * d j (Real.exp r)) ≤ δ) :
    ∃ path : Path (x * vertex 0 * φ z₀) (x * vertex (Fin.last N) * φ z₀),
      PathMetricBound path (L * 2 ^ N) (κ * 2 ^ N) ∧
      ∀ t, ∃ w ∈ E,
        ‖J (path t) - J (x * vertex 0 * φ z₀) - Real.exp r • A w‖ ≤
          2 * Real.exp r * ε + K * δ := by
  have hheight := chain_height_bound_of_common_affine_profile J x vertex 0 r φ q A offset
    Q z₀ hz₀ hgood
  let B := 2 * Real.exp r * ε
  have hbase (i) : ∃ w ∈ A '' E,
      ‖J ((x * vertex i) * φ z₀) - J (x * vertex 0 * φ z₀) - Real.exp r • w‖ ≤ B := by
    refine ⟨0, ⟨0, hE0, A.map_zero⟩, ?_⟩
    simpa only [sub_self, map_zero, smul_zero, sub_zero] using hheight i z₀ hz₀
  have hlegs (i : Fin (N + 1)) (j : Fin N) (t : unitInterval) :
      ∃ w ∈ A '' E,
        ‖J (((x * vertex i) * φ z₀) * d j (Real.exp r * (t : ℝ))) -
          J (x * vertex 0 * φ z₀) - Real.exp r • w‖ ≤ B := by
    refine ⟨A (q (leg j t) - q z₀), mem_image_of_mem A (hlegE j t), ?_⟩
    have hh := hheight i (leg j t) (hleg j t)
    rw [hlegφ] at hh
    simpa only [B, mul_assoc] using hh
  obtain ⟨path, hp, himage⟩ := exists_profile_controlled_support_chain
    (fun i => x * vertex i) (φ z₀) d f hd hd₀ hf hf₀ b
    (fun j => by rw [hstep, mul_assoc]) J hJ (J (x * vertex 0 * φ z₀))
    0 (A '' E) (Real.exp r) B 0 L κ δ hL hκ hδ (by simp) hbase
    (fun j t => hlegs j.castSucc j t) (fun j t => hlegs j.succ j t) hmetric hswitch
  refine ⟨path, hp, ?_⟩
  intro t
  obtain ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, hbound⟩ := himage t
  refine ⟨w, hw, ?_⟩
  simpa only [B, sub_zero, add_zero] using hbound

end PolycyclicRecognition

end

end OAI
