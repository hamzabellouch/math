import OAI.MathematicalPhysics.RapidForcing.Main
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RapidConsequences

namespace OAI

/-!
Compact spatial forcing with slow derivative decay, space-time L² bounds,
and uniformly bounded kinetic energy.

This is Theorem `bcs:scalar-theorem` in *Scalar Potentials and Slow Clocks for
Forced Fluid Computation*, obtained by specializing the rapid decay bounds
of the addressed construction.
-/

noncomputable section
open Set MeasureTheory

namespace RapidForcing

theorem compact_support_slow_decay (ν : ℝ) (hν : 0 < ν)
    (hνcomp : ComputableReal ν) :
    ∃ compile : ℕ → ℕ × ℕ, Computable compile ∧
      ∀ (M : Machine) (w : M.Input),
        let u := addressedVelocity M w
        let f := addressedForce ν M w
        ForceProgram (compile (M.inputDescription w)) f ∧
        Smooth f ∧ Supported f ∧ Smooth u ∧ Supported u ∧
        (∀ l α, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
          ‖mixedD l α u t x‖ + ‖mixedD l α f t x‖ ≤ C * (1 + t)⁻¹ ^ (1 + l)) ∧
        SpaceTimeL2 u ∧ SpaceTimeL2 f ∧
        (∃ E : ℝ, ∀ t, 0 ≤ t → (1 / 2 : ℝ) * ∫ x, ‖u t x‖ ^ 2 ≤ E) ∧
        UniqueEnergySolution ν f u (fun _ _ => 0) ∧
        ∃ X : ℝ → Space → Space, MaterialFlow u X ∧
          (M.Halts w ↔ ∃ t : ℝ, 0 ≤ t ∧ (X t 0) 0 < -1) := by
  obtain ⟨compile, hc, hall⟩ := compact_support_rapid_decay ν hν hνcomp
  refine ⟨compile, hc, fun M w => ?_⟩
  obtain ⟨hp, hfs, hfK, hfr, _, hus, huK, hur, _, hsol, X, hX, hhalt⟩ := hall M w
  obtain ⟨q, hq⟩ := exists_rat_gt ‖ν‖
  have hful2 := (addressedForce_jetControl ν q hq.le M w).spaceTimeL2
  have huul2 := (addressedVelocity_jetControl M w).spaceTimeL2
  have hdecay : ∀ l α, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∀ x,
      ‖mixedD l α (addressedVelocity M w) t x‖ +
        ‖mixedD l α (addressedForce ν M w) t x‖ ≤ C * (1 + t)⁻¹ ^ (1 + l) := by
    intro l α
    obtain ⟨A, hA, hAb⟩ := hur.slowDecay l α
    obtain ⟨B, hB, hBb⟩ := hfr.slowDecay l α
    refine ⟨A + B, add_nonneg hA hB, fun t ht x => ?_⟩
    calc
      _ ≤ A * (1 + t)⁻¹ ^ (1 + l) + B * (1 + t)⁻¹ ^ (1 + l) :=
        add_le_add (hAb t ht x) (hBb t ht x)
      _ = _ := (add_mul _ _ _).symm
  have heb : ∃ E : ℝ, ∀ t, 0 ≤ t →
      (1 / 2 : ℝ) * ∫ x, ‖addressedVelocity M w t x‖ ^ 2 ≤ E := by
    apply supported_uniform_energy
    · intro t
      exact (addressedVelocity_joint_smooth M w).continuous.comp
        (continuous_const.prodMk continuous_id)
    · exact huK
    · obtain ⟨C, hC, hb⟩ := hur 0 0 (fun _ => 0)
      exact ⟨C, hC, fun t ht x => by simpa [mixedD, spatialMulti] using hb t ht x⟩
  exact ⟨hp, hfs, hfK, hus, huK, hdecay, huul2, hful2, heb, hsol, X, hX, hhalt⟩

end RapidForcing

end

end OAI
