import OAI.NumberTheory.Ostmann.Supply.UniformBalanced

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem raw_scalar_bound (S T : Finset (ZMod p)) (K : H →L[ℂ] H) :
    ‖inner ℂ (uniformVector S) (K (uniformVector T))‖ ≤
      ‖uniformVector S‖*‖K‖*‖uniformVector T‖ := by
  calc
    _ ≤ ‖uniformVector S‖*‖K (uniformVector T)‖ := norm_inner_le_norm _ _
    _ ≤ ‖uniformVector S‖*(‖K‖*‖uniformVector T‖) :=
      mul_le_mul_of_nonneg_left (K.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem raw_row_bound (S T : Finset (ZMod p)) (K : H →L[ℂ] H) (v : centeredSpace T) :
    ‖inner ℂ (uniformVector S) (K (v:H))‖ ≤ ‖uniformVector S‖*‖K‖*‖v‖ := by
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [mul_assoc,Submodule.norm_coe] using mul_le_mul_of_nonneg_left (K.le_opNorm (v:H)) (norm_nonneg (uniformVector S)))

theorem raw_column_bound (S T : Finset (ZMod p)) (K : H →L[ℂ] H) :
    ‖centeredProjection S (K (uniformVector T))‖ ≤ ‖K‖*‖uniformVector T‖ :=
  ((centeredSpace S).norm_starProjection_apply_le _).trans (K.le_opNorm _)

theorem raw_lower_bound (S T : Finset (ZMod p)) (K : H →L[ℂ] H) (v : centeredSpace T) :
    ‖centeredProjection S (K (v:H))‖ ≤ ‖K‖*‖v‖ :=
  ((centeredSpace S).norm_starProjection_apply_le _).trans (K.le_opNorm _)

theorem balanced_scalar_bound (S : Finset (ZMod p)) (K : H →L[ℂ] H)
    (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3) :
    ‖inner ℂ (uniformVector S) (K (uniformVector Sᶜ))‖ ≤ 4*‖K‖/(p:ℝ) := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hr : Real.sqrt (p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hS := balanced_uniform_norm S hlo
  have hT := balanced_uniform_norm Sᶜ (balanced_compl S hlo hhi).1
  calc
    _ ≤ ‖uniformVector S‖*‖K‖*‖uniformVector Sᶜ‖ := raw_scalar_bound S Sᶜ K
    _ ≤ (2/Real.sqrt p)*‖K‖*(2/Real.sqrt p) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hS (norm_nonneg _)) hT
        (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
    _ = _ := by
      have hs := Real.sq_sqrt hp.le
      field_simp
      rw [hs]
      ring

end Ostmann.Supply

end

end OAI
