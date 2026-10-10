import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevLocalFlow

namespace OAI

/-! # Local uniqueness of the Sobolev interaction equation -/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- Two Sobolev interaction solutions with the same initial datum agree near that time. -/
theorem sobolevInteractionSolution_eventually_unique
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v w : ℝ → FourierL2)
    (J : Set ℝ) (hJ : IsOpen J) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (hv : ∀ t ∈ J, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hw : ∀ t ∈ J, HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t)
    (heq : v t₀ = w t₀) : v =ᶠ[𝓝 t₀] w := by
  let R := ‖v t₀‖ + 1
  have hR : 0 ≤ R := by positivity
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m R hR
  have hvnorm : ∀ᶠ t in 𝓝 t₀, ‖v t‖ < R :=
    ((hv t₀ ht₀).continuousAt.norm.tendsto).eventually (gt_mem_nhds (by dsimp [R]; linarith))
  have hwnorm : ∀ᶠ t in 𝓝 t₀, ‖w t‖ < R :=
    ((hw t₀ ht₀).continuousAt.norm.tendsto).eventually (gt_mem_nhds (by rw [← heq]; dsimp [R]; linarith))
  apply ODE_solution_unique_of_eventually
    (v := schrodingerInteractionField k hk m) (s := fun _ => closedBall 0 R)
    (K := ⟨K, hK⟩) ?_ ?_ ?_ heq
  · exact Eventually.of_forall (fun t => by
      apply LipschitzOnWith.of_dist_le_mul
      intro f hf g hg
      rw [dist_eq_norm, dist_eq_norm]
      change ‖schrodingerInteractionField k hk m t f - schrodingerInteractionField k hk m t g‖ ≤
        K * ‖f - g‖
      exact hlip t f g (by simpa using hf) (by simpa using hg))
  · filter_upwards [hJ.mem_nhds ht₀, hvnorm] with t ht hn
    exact ⟨hv t ht, by simpa using hn.le⟩
  · filter_upwards [hJ.mem_nhds ht₀, hwnorm] with t ht hn
    exact ⟨hw t ht, by simpa using hn.le⟩

end DefocusingNLS

end OAI
