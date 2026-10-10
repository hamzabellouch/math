import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HeisenbergOffsets
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationCoefficientError

namespace OAI

/-! The actual shifted Heisenberg spectral bottom is stable under edgewise
coefficient errors. This attaches numerical calibration to Hubbard's exact
second-order identity without choosing a nearby exact root. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

theorem graphSourceForm_stability (m : ℕ) (left right : Edge → Fin (m + 1))
    (J K : Edge → ℝ) (u : SourceSpinVector (m + 1)) (hu : sourceSpinMass u = 1) :
    |graphSourceForm m left right J u - graphSourceForm m left right K u| ≤
      4 * ∑ e, |J e - K e| := by
  unfold graphSourceForm
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e, 4 * |J e - K e| := by
      apply Finset.sum_le_sum
      intro e _
      have hf := sourceHeisenbergForm_bounds (left e) (right e) u
      have ha : |sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u| ≤ 4 := by
        rw [hu] at *
        exact abs_le.mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩
      rw [show J e * (sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u) -
          K e * (sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u) =
          (J e - K e) * (sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u) by ring,
        abs_mul]
      exact (mul_le_mul_of_nonneg_left ha (abs_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem graphSourceBottom_minimizer (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ) :
    ∃ u : SourceSpinVector (m + 1), sourceSpinMass u = 1 ∧
      graphSourceBottom m left right J = graphSourceForm m left right J u ∧
      ∀ v : SourceSpinVector (m + 1), sourceSpinMass v = 1 →
        graphSourceForm m left right J u ≤ graphSourceForm m left right J v := by
  let M := finiteHeisenbergMatrix (m + 1) left right J - ((∑ e, J e : ℝ) : ℂ) • 1
  have heq : graphSourceBottom m left right J = sourceMatrixBottom (m + 1) M := by
    dsimp only [M]
    rw [graphSourceBottom_offset, sourceMatrixBottom_shift]
    rfl
  obtain ⟨p, hp, hbottom, hmin⟩ := sourceMatrixBottom_minimizer (m + 1) M
  refine ⟨fun s => p s, ?_, ?_, ?_⟩
  · rw [sourceSpinMass_norm_sq, hp]
    norm_num
  · rw [heq, hbottom]
    exact (graphSourceForm_matrix m left right J p).symm
  · intro v hv
    let q : MediatorLowSpace (m + 1) := WithLp.toLp 2 v
    have hq : ‖q‖ = 1 := by
      have hsq : ‖q‖ ^ 2 = 1 := (sourceSpinMass_norm_sq q).symm.trans hv
      nlinarith [norm_nonneg q]
    rw [graphSourceForm_matrix m left right J p]
    exact (hmin q hq).trans_eq (graphSourceForm_matrix m left right J q).symm

theorem graphSourceBottom_stability (m : ℕ) (left right : Edge → Fin (m + 1)) (J K : Edge → ℝ) :
    |graphSourceBottom m left right J - graphSourceBottom m left right K| ≤
      4 * ∑ e, |J e - K e| := by
  obtain ⟨u, hu, hJu, hJmin⟩ := graphSourceBottom_minimizer m left right J
  obtain ⟨v, hv, hKv, hKmin⟩ := graphSourceBottom_minimizer m left right K
  have hp := graphSourceForm_stability m left right J K u hu
  have hq := graphSourceForm_stability m left right J K v hv
  have hj := hJmin v hv
  have hk := hKmin u hu
  rw [hJu, hKv]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hp).1], by linarith [(abs_le.mp hq).2]⟩

theorem calibrated_graphSourceBottom_error (m : ℕ) (left right : Edge → Fin (m + 1))
    (t K gap ε : Edge → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ e, 0 ≤ K e) (hgap : ∀ e, 0 < gap e)
    (hres : ∀ e, |t e - τ * Real.sqrt (K e * gap e)| ≤ ε e) :
    |graphSourceBottom m left right (fun e => t e ^ 2 / gap e) -
      graphSourceBottom m left right (fun e => τ ^ 2 * K e)| ≤
      4 * ∑ e, ε e * (2 * τ * Real.sqrt (K e * gap e) + ε e) / gap e := by
  apply (graphSourceBottom_stability m left right _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun e _ => calibrated_coefficient_error (hK e) (hgap e) hτ (hres e))

end ContinuumCoulomb.HubbardGlobal

end

end OAI
