import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevPolynomialBounds
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerFlow

namespace OAI

/-! # The interaction representation of the semilinear Schrödinger equation -/

open Filter Topology

namespace DefocusingNLS

/-- Strong continuity and the uniform isometry bound give joint continuity. -/
theorem continuous_schrodingerFlow_uncurry :
    Continuous (fun p : ℝ × FourierL2 => schrodingerFlow p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu : ∀ᶠ q : ℝ × FourierL2 in 𝓝 p, dist q.2 p.2 < ε / 2 :=
    (continuous_snd.continuousAt.tendsto).eventually
      (Metric.ball_mem_nhds p.2 (by linarith))
  have hs : ∀ᶠ q : ℝ × FourierL2 in 𝓝 p,
      dist (schrodingerFlow q.1 p.2) (schrodingerFlow p.1 p.2) < ε / 2 :=
    (((continuous_schrodingerFlow p.2).comp continuous_fst).continuousAt.tendsto).eventually
      (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hu, hs] with q hqu hqs
  calc
    _ ≤ dist (schrodingerFlow q.1 q.2) (schrodingerFlow q.1 p.2) +
        dist (schrodingerFlow q.1 p.2) (schrodingerFlow p.1 p.2) := dist_triangle _ _ _
    _ = dist q.2 p.2 + dist (schrodingerFlow q.1 p.2) (schrodingerFlow p.1 p.2) := by
      rw [(schrodingerFlow q.1).dist_map]
    _ < ε := by linarith

/-- The derivative field for `v(t) = S(-t)u(t)` in the defocusing equation. -/
noncomputable def schrodingerInteractionField (k : ℝ) (hk : 6 < k) (m : ℕ)
    (t : ℝ) (f : FourierL2) : FourierL2 :=
  (-Complex.I) • schrodingerFlow (-t) (sobolevOddPower k hk m (schrodingerFlow t f))

theorem continuous_schrodingerInteractionField (k : ℝ) (hk : 6 < k) (m : ℕ) :
    Continuous (fun p : ℝ × FourierL2 => schrodingerInteractionField k hk m p.1 p.2) := by
  have hN : Continuous (fun p : ℝ × FourierL2 =>
      sobolevOddPower k hk m (schrodingerFlow p.1 p.2)) :=
    (contDiff_sobolevOddPower k hk m).continuous.comp continuous_schrodingerFlow_uncurry
  exact (continuous_schrodingerFlow_uncurry.comp
    ((continuous_fst.neg).prodMk hN)).const_smul (-Complex.I)

theorem norm_schrodingerInteractionField (k : ℝ) (hk : 6 < k) (m : ℕ)
    (t : ℝ) (f : FourierL2) :
    ‖schrodingerInteractionField k hk m t f‖ =
      ‖sobolevOddPower k hk m (schrodingerFlow t f)‖ := by
  simp [schrodingerInteractionField, norm_smul]

theorem norm_schrodingerInteractionField_sub (k : ℝ) (hk : 6 < k) (m : ℕ)
    (t : ℝ) (f g : FourierL2) :
    ‖schrodingerInteractionField k hk m t f - schrodingerInteractionField k hk m t g‖ =
      ‖sobolevOddPower k hk m (schrodingerFlow t f) -
        sobolevOddPower k hk m (schrodingerFlow t g)‖ := by
  unfold schrodingerInteractionField
  rw [← smul_sub, ← map_sub, norm_smul, LinearIsometry.norm_map]
  simp

/-- The interaction vector field has time-uniform bounds and Lipschitz constants on norm balls. -/
theorem exists_schrodingerInteractionField_ball_bounds (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      (∀ t (f : FourierL2), ‖f‖ ≤ R → ‖schrodingerInteractionField k hk m t f‖ ≤ A) ∧
      (∀ t (f g : FourierL2), ‖f‖ ≤ R → ‖g‖ ≤ R →
        ‖schrodingerInteractionField k hk m t f -
          schrodingerInteractionField k hk m t g‖ ≤ K * ‖f - g‖) := by
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ := exists_sobolevOddPower_ball_bounds k hk m R hR
  refine ⟨A, K, hA, hK, ?_, ?_⟩
  · intro t f hf
    rw [norm_schrodingerInteractionField]
    exact hbound _ (by simpa using hf)
  · intro t f g hf hg
    rw [norm_schrodingerInteractionField_sub]
    have h := hlip (schrodingerFlow t f) (schrodingerFlow t g)
      (by simpa using hf) (by simpa using hg)
    simpa only [← map_sub, LinearIsometry.norm_map] using h

end DefocusingNLS

end OAI
