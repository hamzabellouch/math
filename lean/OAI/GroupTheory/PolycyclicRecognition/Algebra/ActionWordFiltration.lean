import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearActionFiltration

namespace OAI

/-! # Operator words and the action filtration

The image-span filtration is controlled by products of the operators. This
turns any uniform vanishing length into the dimension bound proved for that
filtration.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def actionOperatorWord (D : I → Module.End K V) (w : List I) : Module.End K V :=
  (w.map D).prod

theorem linearActionFiltration_le_ker (D : I → Module.End K V) (n : ℕ)
    (f : Module.End K V)
    (h : ∀ w : List I, w.length = n → f * actionOperatorWord D w = 0) :
    linearActionFiltration D n ≤ LinearMap.ker f := by
  induction n generalizing f with
  | zero =>
    have hf : f = 0 := by simpa [actionOperatorWord] using h [] rfl
    simp [hf]
  | succ n ih =>
    change (⨆ i, (linearActionFiltration D n).map (D i)) ≤ LinearMap.ker f
    apply iSup_le
    intro i
    rintro y ⟨x, hx, rfl⟩
    have hk := ih (f * D i) (by
      intro w hw
      have he := h (i :: w) (by simp [hw])
      simpa only [actionOperatorWord, List.map_cons, List.prod_cons, mul_assoc] using he)
    exact hk hx

theorem linearActionFiltration_eq_bot_of_word_zero
    (D : I → Module.End K V) (n : ℕ)
    (h : ∀ w : List I, w.length = n → actionOperatorWord D w = 0) :
    linearActionFiltration D n = ⊥ := by
  apply eq_bot_iff.mpr
  have he := linearActionFiltration_le_ker D n 1 (by simpa using h)
  simpa only [Module.End.one_eq_id, LinearMap.ker_id] using he

theorem actionOperatorWord_apply_mem (D : I → Module.End K V)
    (w : List I) (v : V) :
    actionOperatorWord D w v ∈ linearActionFiltration D w.length := by
  induction w with
  | nil => exact Submodule.mem_top
  | cons i w ih =>
    change D i (actionOperatorWord D w v) ∈
      ⨆ j, (linearActionFiltration D w.length).map (D j)
    exact (le_iSup (fun j => (linearActionFiltration D w.length).map (D j)) i)
      ⟨actionOperatorWord D w v, ih, rfl⟩

theorem actionOperatorWord_zero_of_filtration_eq_bot
    (D : I → Module.End K V) {n : ℕ} (h : linearActionFiltration D n = ⊥)
    (w : List I) (hw : w.length = n) : actionOperatorWord D w = 0 := by
  apply LinearMap.ext
  intro v
  have hv := actionOperatorWord_apply_mem D w v
  rw [hw, h] at hv
  exact hv

theorem actionOperatorWord_zero_at_finrank [Module.Finite K V]
    (D : I → Module.End K V)
    (h : ∃ c, ∀ w : List I, w.length = c → actionOperatorWord D w = 0) :
    ∀ w : List I, w.length = Module.finrank K V → actionOperatorWord D w = 0 := by
  apply actionOperatorWord_zero_of_filtration_eq_bot
  apply linearActionFiltration_finrank_eq_bot
  obtain ⟨c, hc⟩ := h
  exact ⟨c, linearActionFiltration_eq_bot_of_word_zero D c hc⟩

end PolycyclicRecognition

end

end OAI
