import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesSums

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum

theorem sum_norm_le_totient {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]
    (F : (ι → (ZMod N)ˣ) → ℂ) {B : ℝ} (hF : ∀x, ‖F x‖ ≤ B) :
    (∑x, ‖F x‖) ≤ (N.totient:ℝ)^(Fintype.card ι)*B := by
  classical
  calc
    _ ≤ ∑ _x : ι → (ZMod N)ˣ, B := Finset.sum_le_sum (fun x _ => hF x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fun, ZMod.card_units_eq_totient, Nat.cast_pow]

theorem sum_norm_le_modulus_power {ι : Type*} [Fintype ι] [DecidableEq ι] {N D a : ℕ} [NeZero N]
    (hD : D ≤ N) (F : (ι → (ZMod N)ˣ) → ℂ)
    (hF : ∀x, ‖F x‖ ≤ (D:ℝ)^a) :
    (∑x, ‖F x‖) ≤ (N:ℝ)^(Fintype.card ι+a) := by
  calc
    _ ≤ (N.totient:ℝ)^(Fintype.card ι)*(D:ℝ)^a := sum_norm_le_totient F hF
    _ ≤ (N:ℝ)^(Fintype.card ι)*(N:ℝ)^a := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.totient_le N) _
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hD) _
      · positivity
      · positivity
    _ = _ := (pow_add _ _ _).symm

theorem ordered_sum_norm_le_modulus_power {N D a l m : ℕ} [NeZero N]
    (hD : D ≤ N) (F : (Fin (2^l)×Fin m → (ZMod N)ˣ) → ℂ)
    (hF : ∀x, ‖F x‖ ≤ (D:ℝ)^a) :
    (∑x, ‖F x‖) ≤ (N:ℝ)^(2^l*m+a) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using sum_norm_le_modulus_power hD F hF

theorem history_exponent_le {l k : ℕ} (hl : l ≤ k) : 2^(l+1) ≤ 3+2^(k+1) :=
  (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (Nat.add_le_add_right hl 1)).trans (Nat.le_add_left _ _)

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
