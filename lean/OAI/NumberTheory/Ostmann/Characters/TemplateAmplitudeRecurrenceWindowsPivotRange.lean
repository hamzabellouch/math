import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateExternal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def pivotWindow (T W : ℝ) : Finset ℕ+ :=
  ((Finset.Icc 1 ⌊Real.exp (T+W)⌋₊).subtype (fun n : ℕ => 0 < n)).filter
    (fun P => Real.exp (T-W) ≤ (P:ℝ))

@[simp] theorem mem_pivotWindow (T W : ℝ) (P : ℕ+) :
    P ∈ pivotWindow T W ↔ Real.exp (T-W) ≤ (P:ℝ) ∧ (P:ℝ) ≤ Real.exp (T+W) := by
  rcases P with ⟨n,hn⟩
  change (⟨n,hn⟩ : {n : ℕ // 0 < n}) ∈
    ((Finset.Icc 1 ⌊Real.exp (T+W)⌋₊).subtype (fun n : ℕ => 0 < n)).filter
      (fun P => Real.exp (T-W) ≤ (P.val:ℝ)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_subtype, Finset.mem_Icc]
  have hP : 1 ≤ n := hn
  rw [Nat.le_floor_iff (Real.exp_pos (T+W)).le]
  exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨hP,h.2⟩,h.1⟩⟩

theorem pivotWindow_lower (T W : ℝ) {P : ℕ+} (hP : P ∈ pivotWindow T W) :
    Real.exp (T-W) ≤ (P:ℝ) := (mem_pivotWindow T W P).mp hP |>.1

theorem pivotWindow_upper (T W : ℝ) {P : ℕ+} (hP : P ∈ pivotWindow T W) :
    (P:ℝ) ≤ Real.exp (T+W) := (mem_pivotWindow T W P).mp hP |>.2

theorem pivotWindow_card_le (T W : ℝ) :
    ((pivotWindow T W).card:ℝ) ≤ Real.exp (T+W) :=
  DiagonalEstimate.positive_product_count_le (pivotWindow T W) (T+W)
    (fun _ hP => pivotWindow_upper T W hP)

theorem mem_pivotWindow_iff_log (T W : ℝ) (P : ℕ+) :
    P ∈ pivotWindow T W ↔ T-W ≤ Real.log (P:ℝ) ∧ Real.log (P:ℝ) ≤ T+W := by
  have hP : 0 < (P:ℝ) := by exact_mod_cast P.pos
  rw [mem_pivotWindow]
  constructor
  · intro h
    constructor
    · apply Real.exp_le_exp.mp
      simpa only [Real.exp_log hP] using h.1
    · apply Real.exp_le_exp.mp
      simpa only [Real.exp_log hP] using h.2
  · intro h
    constructor
    · simpa only [Real.exp_log hP] using Real.exp_le_exp.mpr h.1
    · simpa only [Real.exp_log hP] using Real.exp_le_exp.mpr h.2

theorem mem_pivotWindow_iff_abs_log (T W : ℝ) (P : ℕ+) :
    P ∈ pivotWindow T W ↔ |Real.log (P:ℝ)-T| ≤ W := by
  rw [mem_pivotWindow_iff_log,abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem pivotWindow_mono_width (T : ℝ) {W W' : ℝ} (h : W ≤ W') :
    pivotWindow T W ⊆ pivotWindow T W' := by
  intro P hP
  rw [mem_pivotWindow_iff_abs_log] at hP ⊢
  exact hP.trans h

end Ostmann.Characters.Template

end

end OAI
