import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreReference
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def originalMean (w : ι → ℝ) (v : κ → ℝ) (F : ι → κ → ℂ) : ℂ :=
  ∑ x, ∑ y, ((w x*v y:ℝ):ℂ)*F x y

theorem originalMean_eq_nested (w : ι → ℝ) (v : κ → ℝ) (F : ι → κ → ℂ) :
    originalMean w v F = ∑ x, (w x:ℂ)*(∑ y, (v y:ℂ)*F x y) := by
  unfold originalMean
  simp only [Finset.mul_sum,Complex.ofReal_mul,mul_assoc]

theorem originalMean_eq_zero_or_reference
    (w : ι → ℝ) (v : κ → ℝ) (F : ι → κ → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (Valid : ι → κ → Prop)
    (hvalid : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y ≠ 0 → Valid x y) :
    originalMean w v F = 0 ∨
      ∃ x y, 0 < w x ∧ 0 < v y ∧ F x y ≠ 0 ∧ Valid x y := by
  classical
  by_cases hmean : originalMean w v F = 0
  · exact Or.inl hmean
  · right
    have hsum : (∑ x, ∑ y, ((w x*v y:ℝ):ℂ)*F x y) ≠ 0 := hmean
    obtain ⟨x,_,hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    obtain ⟨y,_,hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hw0 : w x ≠ 0 := by intro h; apply hy; simp [h]
    have hv0 : v y ≠ 0 := by intro h; apply hy; simp [h]
    have hf0 : F x y ≠ 0 := by intro h; apply hy; simp [h]
    exact ⟨x,y,lt_of_le_of_ne (hw x) (Ne.symm hw0),
      lt_of_le_of_ne (hv y) (Ne.symm hv0),hf0,hvalid x y hw0 hv0 hf0⟩

theorem originalMean_congr (w : ι → ℝ) (v : κ → ℝ) (F T : ι → κ → ℂ)
    (h : ∀ x y, w x ≠ 0 → v y ≠ 0 → F x y = T x y) :
    originalMean w v F = originalMean w v T := by
  unfold originalMean
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : w x = 0
  · simp only [hx,zero_mul,Complex.ofReal_zero]
  by_cases hy : v y = 0
  · simp only [hy,mul_zero,Complex.ofReal_zero,zero_mul]
  rw [h x y hx hy]

end Ostmann.Arithmetic.HistoryBulkFibreReference

end

end OAI
