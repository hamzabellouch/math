import Mathlib
import OAI.Geometry.RecorderBoxes.Affine
import OAI.Computability.SolenoidalRecorder.Halting

namespace OAI

/-! Configuration codes, unique affine branches and terminal observation strips. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
noncomputable def configCode {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (c : Recorder.Config M) : ℝ × ℝ :=
  place c.control (Radix.tapeCode (fun k => e (c.tape k)) c.head)

 

theorem step_has_affine_branch {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {c c' : Recorder.Config M} (hc : Recorder.Step c c') :
    ∃ i : Branch M, configCode e c ∈ (sourceRectangle e i).carrier ∧
      affine e i (configCode e c) = configCode e c' := by
  obtain ⟨s, b, d, hr, rfl⟩ := hc
  let i : Branch M := ⟨c.control, c.tape c.head, c.tape (c.head - 1), s, b, d, hr⟩
  refine ⟨i, ?_, ?_⟩
  · rw [sourceRectangle, physicalBox_carrier]
    refine ⟨Radix.tapeCode (fun k => e (c.tape k)) c.head, ?_, rfl⟩
    exact Radix.tapeCode_mem_source (fun k => e (c.tape k)) c.head
  · have ht : (fun k => e (Function.update c.tape c.head b k)) =
        Function.update (fun k => e (c.tape k)) c.head (e b) := by
      funext k
      by_cases hk : k = c.head
      · subst k; simp
      · simp [hk]
    dsimp only [affine, configCode, i]
    rw [unplace_place, Radix.update_tapeCode (fun k => e (c.tape k)) c.head (e b) d]
    simp only [Recorder.successor, ht]

 

theorem step_has_unique_affine_branch {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {c c' : Recorder.Config M} (hc : Recorder.Step c c') :
    ∃! i : Branch M, configCode e c ∈ (sourceRectangle e i).carrier ∧
      affine e i (configCode e c) = configCode e c' := by
  obtain ⟨i, hi, ht⟩ := step_has_affine_branch e hc
  refine ⟨i, ⟨hi, ht⟩, ?_⟩
  intro j hj
  by_contra hne
  have hgap := source_rectangles_separated e hne
  have hg : 0 < kappa M / Radix.base m ^ 2 :=
    div_pos (kappa_pos M) (pow_pos (Radix.base_pos m) _)
  exact Set.disjoint_left.mp (Rectangle.disjoint_of_gap hg hgap) hj.1 hi

 
theorem configCode_bounds {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (c : Recorder.Config M) :
    origin c.control ≤ (configCode e c).1 ∧
    (configCode e c).1 ≤ origin c.control + kappa M ∧
    (3 / 8 : ℝ) ≤ (configCode e c).2 ∧
    (configCode e c).2 ≤ 3 / 8 + kappa M := by
  have hL := Radix.code_bounds (Radix.leftStack (fun k => e (c.tape k)) c.head)
  have hR := Radix.code_bounds (Radix.rightStack (fun k => e (c.tape k)) c.head)
  have hL₀ := mul_nonneg (kappa_pos M).le hL.1
  have hR₀ := mul_nonneg (kappa_pos M).le hR.1
  have hL₁ := mul_le_mul_of_nonneg_left hL.2 (kappa_pos M).le
  have hR₁ := mul_le_mul_of_nonneg_left hR.2 (kappa_pos M).le
  dsimp [configCode, Radix.tapeCode, place]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem terminalControl_iff (c : Recorder.Config M) :
    terminalControl c.control = true ↔ Recorder.Terminal c := by
  cases h : c.control <;> simp [terminalControl, Recorder.Terminal, h]

 
theorem terminal_code_range {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {c : Recorder.Config M} (hc : Recorder.Terminal c) :
    (3 / 4 : ℝ) ≤ (configCode e c).1 ∧ (configCode e c).1 < 13 / 16 := by
  have h := (terminalControl_iff c).mpr hc
  have hs := state_extent c.control
  simp only [h, ↓reduceIte] at hs
  have hb := configCode_bounds e c
  exact ⟨hs.1.trans hb.1, hb.2.1.trans_lt hs.2⟩

 

theorem nonterminal_code_range {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {c : Recorder.Config M} (hc : ¬Recorder.Terminal c) :
    (1 / 8 : ℝ) ≤ (configCode e c).1 ∧ (configCode e c).1 < 3 / 16 := by
  have hf : terminalControl c.control = false := by
    cases he : terminalControl c.control with
    | false => rfl
    | true => exact False.elim (hc ((terminalControl_iff c).mp he))
  have hs := state_extent c.control
  simp only [hf, Bool.false_eq_true, ↓reduceIte] at hs
  have hb := configCode_bounds e c
  exact ⟨hs.1.trans hb.1, hb.2.1.trans_lt hs.2⟩
end Bridge
end Solenoidal

end OAI
