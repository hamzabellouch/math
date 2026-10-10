import OAI.NumberTheory.JointDickman.Counting.ResidueCoarseShort

namespace OAI

/-! # Exact passage between discrete and continuous short-window energy -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem complexShortAverage_integer_cell (f : ArithmeticFunction ℂ) (H u : ℕ)
    {z : ℝ} (hz : (u : ℝ) < z ∧ z < (u : ℝ)+1) :
    complexShortAverage f H z = complexShortAverage f H u := by
  have hz0 : 0 ≤ z := (Nat.cast_nonneg u).trans hz.1.le
  have hf : ⌊z⌋₊ = u := (Nat.floor_eq_iff hz0).mpr ⟨hz.1.le,hz.2⟩
  have hfH : ⌊z+(H : ℝ)⌋₊ = u+H := by rw [Nat.floor_add_natCast hz0,hf]
  simp only [complexShortAverage,hf,hfH,Nat.floor_natCast,← Nat.cast_add]

theorem complexShortAverage_cell_integral (f : ArithmeticFunction ℂ) (H u : ℕ) :
    (∫ z in (u : ℝ)..(u+1 : ℕ), ‖complexShortAverage f H z‖^2) =
      ‖complexShortAverage f H u‖^2 := by
  calc
    _ = ∫ _z in (u : ℝ)..(u+1 : ℕ), ‖complexShortAverage f H u‖^2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_cast; omega)
      intro z hz
      exact congrArg (fun w : ℂ => ‖w‖^2)
        (complexShortAverage_integer_cell f H u (z := z) (by simpa using hz))
    _ = _ := by simp

theorem complexShortAverage_discrete_energy (f : ArithmeticFunction ℂ) {H : ℕ}
    (hH : 0 < H) (a b : ℕ) (hab : a ≤ b) :
    (∑ u ∈ Ico a b, ‖complexShortAverage f H u‖^2) =
      ∫ z in (a : ℝ)..(b : ℝ), ‖complexShortAverage f H z‖^2 := by
  have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun u : ℕ => (u : ℝ))
    (f := fun z => ‖complexShortAverage f (H : ℝ) z‖^2) (μ := volume) hab
    (fun u _ => by
      simpa only [Nat.cast_add,Nat.cast_one] using
        complexShortAverage_sq_integrable_any f (H := (H : ℝ)) (by exact_mod_cast hH) u (u+1))
  simpa only [complexShortAverage_cell_integral] using h

theorem residueBinAverage_discrete_energy {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) (a b : ℕ) (hab : a ≤ b) :
    (∑ u ∈ Ico a b, ‖residueBinAverage E ζ μ w r H u‖^2) =
      ∫ z in (a : ℝ)..(b : ℝ), ‖residueBinAverage E ζ μ w r H z‖^2 := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_discrete_energy f hH a b hab

end JointDickman

end OAI
