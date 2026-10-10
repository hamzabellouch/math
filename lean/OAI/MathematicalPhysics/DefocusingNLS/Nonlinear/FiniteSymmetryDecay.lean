import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryBackward
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # A diagonal nonnegative symmetry orbit cannot decay to zero -/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS

theorem finite_symmetry_exp_decay_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (G : V →L[ℂ] V)
    (hspan : (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤)
    (hspec : ∀ (lam : ℂ) (v : V), v ≠ 0 → G v = lam • v → lam = 0 ∨ lam = 1 ∨ lam = 1 / 2)
    (u : V) (D δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ t : ℝ≥0, ‖NormedSpace.exp ((t : ℝ) • G) u‖ ≤ D * Real.exp (-δ * (t : ℝ))) :
    u = 0 := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let e := symmetryCoordinateEquiv G hspan hspec
  let c := e.symm u
  have hb (t : ℝ≥0) : ‖c‖ ≤ ‖e.symm.toContinuousLinearMap‖ *
      (D * Real.exp (-δ * (t : ℝ))) := by
    have he : symmetryCoordinateEvolution G t c = e.symm (NormedSpace.exp ((t : ℝ) • G) u) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (symmetryCoordinateEvolution_intertwines G t c).symm.trans
        (congrArg (fun x : V => (NormedSpace.exp ((t : ℝ) • G) : V →L[ℂ] V) x)
          (e.apply_symm_apply u))
    have hi : c = symmetryCoordinateEvolution G (-(t : ℝ))
        (e.symm (NormedSpace.exp ((t : ℝ) • G) u)) := by
      rw [← he]
      simpa only [neg_neg] using (symmetryCoordinateEvolution_inverse G (-(t : ℝ)) c).symm
    calc
      ‖c‖ = ‖symmetryCoordinateEvolution G (-(t : ℝ))
          (e.symm (NormedSpace.exp ((t : ℝ) • G) u))‖ := congrArg norm hi
      _ ≤ ‖e.symm (NormedSpace.exp ((t : ℝ) • G) u)‖ := by
        simpa only [one_mul] using (symmetryCoordinateEvolution G (-(t : ℝ))).le_of_opNorm_le
          (symmetryCoordinateEvolution_backward_norm G t t.2) _
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖NormedSpace.exp ((t : ℝ) • G) u‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdecay t) (norm_nonneg e.symm.toContinuousLinearMap)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => ‖e.symm.toContinuousLinearMap‖ *
      (D * Real.exp (-δ * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by linarith))))
  have hc : ‖c‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => hb n)
  have hc0 : c = 0 := norm_eq_zero.mp (le_antisymm hc (norm_nonneg _))
  exact e.symm.injective (hc0.trans (map_zero e.symm).symm)

end DefocusingNLS

end OAI
