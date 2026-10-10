import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairPathMesh

namespace OAI

/-! # Finite meshes for paths with short jumps

The support-switch construction has a bounded number of logarithmically
short switches. An additive coarse error in its parameterized path therefore
contributes only the corresponding additive error to the height comparison.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G W T : Type*} [Group G] [MetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoMetricSpace T] {Λ : ℝ≥0}

/-- Sampled height estimates control a whole coarse path, retaining the
additive distance error explicitly. -/
theorem coarse_image_path_height_control
    (p : NormalizedPair G Λ) (π : G →* Multiplicative W) (l : G →* Multiplicative W)
    {Lπ L r δ η ε κ : ℝ} (hLπ : 0 ≤ Lπ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Lπ * dist x y)
    (γ : T → G) (hγ : ∀ t u, dist (γ t) (γ u) ≤ L * r * dist t u + κ)
    (S : Finset T) (hmesh : ∀ t, ∃ u ∈ S, dist t u ≤ δ)
    (E : Set W)
    (hheight : ∀ u ∈ S, ∃ w ∈ E, ‖(l (γ u)).toAdd - r • w‖ ≤ ε * r)
    (herror : ∀ u ∈ S, ‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ ≤ η * r) :
    ∀ t, ∃ w ∈ E,
      ‖pairHeight π (γ t) p - r • w‖ ≤
        (Lπ * Λ * L * δ + η + ε) * r + Lπ * Λ * κ := by
  intro t
  obtain ⟨u, hu, htu⟩ := hmesh t
  obtain ⟨w, hw, hwu⟩ := hheight u hu
  refine ⟨w, hw, ?_⟩
  have hdist : dist (γ t) (γ u) ≤ L * r * δ + κ :=
    (hγ t u).trans (by
      linarith [mul_le_mul_of_nonneg_left htu (mul_nonneg hL hr)])
  have hF := p.property.1.1.dist_le_mul (γ t) (γ u)
  have hp : ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ ≤
      Lπ * Λ * (L * r * δ + κ) := by
    apply (hπ (p.val.1 (γ t)) (p.val.1 (γ u))).trans
    calc
      _ ≤ Lπ * (Λ * dist (γ t) (γ u)) := mul_le_mul_of_nonneg_left hF hLπ
      _ ≤ Lπ * (Λ * (L * r * δ + κ)) := by gcongr
      _ = _ := by ring
  have triangle (a b c : W) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  calc
    _ ≤ ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ +
        ‖pairHeight π (γ u) p - r • w‖ := triangle _ _ _
    _ ≤ Lπ * Λ * (L * r * δ + κ) +
        (‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ +
          ‖(l (γ u)).toAdd - r • w‖) := add_le_add hp (triangle _ _ _)
    _ ≤ Lπ * Λ * (L * r * δ + κ) + (η * r + ε * r) :=
      add_le_add le_rfl (add_le_add (herror u hu) hwu)
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
