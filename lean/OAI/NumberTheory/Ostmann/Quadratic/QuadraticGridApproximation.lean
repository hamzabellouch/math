import OAI.NumberTheory.Ostmann.Quadratic.QuadraticParameterGrid

namespace OAI

/-! # Approximation of the original quadratic series by the fixed grid -/

namespace Ostmann

open scoped SchwartzMap

noncomputable def quadraticGridError (q s : ℕ) (B Rmax v H : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℝ :=
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H +
    Real.sqrt ((s : ℝ) * v / q) * W * B *
      (SchwartzMap.seminorm ℝ 0 0 Φ +
        SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2)

theorem positiveQuadraticSum_parameter_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' Rmax v H δ : ℝ) (s : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hRR : R ≤ Rmax) (hR'R : R' ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hθδ : |θ - θ'| ≤ δ) (hRδ : |R - R'| ≤ δ)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R' v s‖ ≤
      quadraticGridError q s B Rmax v H Φ * δ := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hR0 : 0 < R := by linarith
  have hRmax0 : 0 ≤ Rmax := by linarith
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  let Cθ := B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H
  let CR := Real.sqrt ((s : ℝ) * v / q) * W * B *
    (SchwartzMap.seminorm ℝ 0 0 Φ +
      SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2)
  have hCθ : 0 ≤ Cθ := by dsimp [Cθ]; positivity
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  have hphase : ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s‖ ≤
      Cθ * δ := by
    apply (positiveQuadraticSum_phase_sub_bound g B hg a θ θ' Φ R v H s hR0 hv hH hs hΦ).trans
    dsimp [Cθ]
    calc
      _ ≤ B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax * δ) * Real.sqrt H := by gcongr
      _ = _ := by ring
  have hscale : ‖positiveQuadraticSum g a θ' Φ R v s - positiveQuadraticSum g a θ' Φ R' v s‖ ≤
      CR * δ := by
    apply (positiveQuadraticSum_scale_sub_bound g B hg a θ' Φ R R' Rmax v H s
      hR hR' hRR hR'R hv hH hs hΦ).trans
    exact mul_le_mul_of_nonneg_left hRδ hCR
  have he : positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R' v s =
      (positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s) +
      (positiveQuadraticSum g a θ' Φ R v s - positiveQuadraticSum g a θ' Φ R' v s) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add hphase hscale).trans_eq
  change Cθ * δ + CR * δ = (Cθ + CR) * δ
  ring

theorem positiveQuadraticSum_grid_approximation {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R Rmax v H δ : ℝ) (s : ℕ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR : 1 ≤ R) (hRR : R ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s) (hδ : 0 < δ)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∃ j ∈ quadraticParameterGrid Rmax δ,
      0 ≤ quadraticGridPhase δ j ∧ quadraticGridPhase δ j ≤ 1 ∧
      1 ≤ quadraticGridScale δ j ∧ quadraticGridScale δ j ≤ Rmax ∧
      ‖positiveQuadraticSum g a θ Φ R v s -
        positiveQuadraticSum g a (quadraticGridPhase δ j) Φ (quadraticGridScale δ j) v s‖ ≤
        quadraticGridError q s B Rmax v H Φ * δ := by
  obtain ⟨j, hj, hjθ0, hjθ, hjR1, hjR, hjθδ, hjRδ⟩ :=
    quadraticParameterGrid_covers Rmax δ θ R hδ hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ.trans hθ1, hjR1, hjR.trans hRR, ?_⟩
  exact positiveQuadraticSum_parameter_sub_bound g B hg a θ (quadraticGridPhase δ j) Φ
    R (quadraticGridScale δ j) Rmax v H δ s hR hjR1 hRR (hjR.trans hRR)
    hv hH hs hjθδ.le hjRδ.le hΦ

end Ostmann

end OAI
