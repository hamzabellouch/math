import OAI.NumberTheory.Ostmann.Conclusion.RegularNormCell

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression
open Ostmann.Construction

theorem regular_harmonicIntegral_le (M : ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (horder : lo ≤ hi) (hwidth : hi-lo ≤ 1) :
    harmonicIntegral M lo hi ≤ (M.totient : ℝ)⁻¹/lo := by
  have hhi : 0 < hi := hlo.trans_le horder
  have hh := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
  have hfrac : hi/lo-1 ≤ 1/lo := by
    apply (le_div_iff₀ hlo).mpr
    field_simp
    nlinarith
  rw [harmonicIntegral,integral_inv_of_pos hlo hhi]
  calc
    _ ≤ (M.totient : ℝ)⁻¹*(1/lo) := mul_le_mul_of_nonneg_left (hh.trans hfrac) (by positivity)
    _ = _ := by ring

theorem unitTest_nonneg {M : ℕ} [NeZero M]
    (F : (ZMod M)ˣ → ℝ) (hF : ∀ u, 0 ≤ F u) (x : ZMod M) : 0 ≤ unitTest F x := by
  unfold unitTest
  exact Finset.sum_nonneg fun u _ => by split_ifs <;> simp only [hF,le_refl]

theorem regular_cell_principal_le {M : ℕ} [NeZero M] {c Z lo hi : ℝ}
    (hc : 2 ≤ c) (hZ : 0 < Z) (hZinv : Z⁻¹ ≤ 2*c)
    (hratio : (M : ℝ)/(M.totient : ℝ) ≤ 2)
    (hlo : c-1 ≤ lo) (horder : lo ≤ hi) (hwidth : hi-lo ≤ 1) :
    (harmonicIntegral M lo hi/Z)*(M : ℝ) ≤ 8 := by
  have hlo0 : 0 < lo := by linarith
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos M)
  have hmain := regular_harmonicIntegral_le M hlo0 horder hwidth
  have hc0 : 0 < c := by linarith
  have hinv : lo⁻¹ ≤ 2/c := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hlo0 hc0).mpr
    nlinarith
  calc
    _ ≤ (((M.totient : ℝ)⁻¹/lo)/Z)*(M : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmain hZ.le) (Nat.cast_nonneg M)
    _ = ((M : ℝ)/(M.totient : ℝ))*lo⁻¹*Z⁻¹ := by ring
    _ ≤ 2*(2/c)*(2*c) := mul_le_mul
      (mul_le_mul hratio hinv (by positivity) (by norm_num)) hZinv (by positivity) (by positivity)
    _ = 8 := by field_simp; norm_num

end Ostmann.Conclusion

end

end OAI
