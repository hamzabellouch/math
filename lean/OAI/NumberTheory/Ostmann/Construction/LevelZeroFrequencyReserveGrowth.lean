import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencyReserve

namespace OAI

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped Topology

theorem initialGap_le_linear (Bs : ℝ) (k : ℕ) {L : ℝ} (hL : 0≤L) :
    Conclusion.initialGap Bs k L ≤
      (|Bs+8*Real.log (Conclusion.bulkScale k)| * Conclusion.bulkScale k)*L := by
  unfold Conclusion.initialGap
  calc
    _ ≤ |Bs+8*Real.log (Conclusion.bulkScale k)| * (Conclusion.bulkSize k L:ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
    _ ≤ |Bs+8*Real.log (Conclusion.bulkScale k)| * (Conclusion.bulkScale k*L) :=
      mul_le_mul_of_nonneg_left (Conclusion.bulkSize_bounds k hL).2 (abs_nonneg _)
    _ = _ := by ring

theorem eventually_levelZero_window_doubleExp (Bs : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (Conclusion.initialGap Bs k L+levelZeroSupportWidth k) <
        Real.exp (Real.exp ((1/2000:ℝ)*L)) := by
  let C : ℝ := |Bs+8*Real.log (Conclusion.bulkScale k)| * Conclusion.bulkScale k
  have hlin := (isLittleO_pow_exp_pos_mul_atTop 1
    (by norm_num : (0:ℝ)<1/2000)).const_mul_left C
  have hconst := (isLittleO_pow_exp_pos_mul_atTop 0
    (by norm_num : (0:ℝ)<1/2000)).const_mul_left (levelZeroSupportWidth k)
  have hb := (hlin.add hconst).bound (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with L hb hL
  have hgap := initialGap_le_linear Bs k hL
  change Conclusion.initialGap Bs k L≤C*L at hgap
  have hpos : 0≤C*L+levelZeroSupportWidth k := by
    dsimp [C,Conclusion.bulkScale,levelZeroSupportWidth]
    positivity
  simp only [pow_one,pow_zero,mul_one,Real.norm_eq_abs,
    abs_of_nonneg hpos,abs_of_pos (Real.exp_pos _)] at hb
  apply Real.exp_lt_exp.mpr
  have he : 0<Real.exp ((1/2000:ℝ)*L) := Real.exp_pos _
  linarith

end Ostmann.Construction

end

end OAI
