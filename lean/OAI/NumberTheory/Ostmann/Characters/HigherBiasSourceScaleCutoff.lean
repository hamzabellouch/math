import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceScale
import OAI.NumberTheory.Ostmann.Preliminaries.CollisionScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Filter Preliminaries

theorem eventually_log_quarter_le_collisionScale10 :
    ∀ᶠ X : ℕ in atTop,∀ p : ℕ,
      Real.log (p:ℝ) ≤ Real.log (X:ℝ)/4 → p ≤ collisionScale 10 X := by
  have hlogt : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/88)
  filter_upwards [eventually_collisionScale_conditions 10,hlogt.eventually hsmall,
    hlogt.eventually_ge_atTop (8*Real.log 2)] with X hX hs hlarge
  have hh := collisionScale_estimates 10 X hX.1 hX.2.1 hX.2.2
  have hln : 0 ≤ Real.log (X:ℝ) := by linarith [hX.2.1]
  have hll : 0 ≤ Real.log (Real.log (X:ℝ)) := Real.log_nonneg hX.2.1
  simp only [Real.norm_eq_abs,id_eq,abs_of_nonneg hln,abs_of_nonneg hll] at hs
  have hcut : Real.log (X:ℝ)/4 ≤ Real.log (collisionScale 10 X:ℝ) := by
    have he := hh.2.1
    norm_num at he
    nlinarith
  intro p hp
  by_cases hp0 : p=0
  · subst p
    exact Nat.zero_le _
  have hpp : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hqp : (0:ℝ)<collisionScale 10 X := by exact_mod_cast (show 0<collisionScale 10 X by omega)
  have hcmp := Real.exp_le_exp.mpr (hp.trans hcut)
  rw [Real.exp_log hpp,Real.exp_log hqp] at hcmp
  exact_mod_cast hcmp

theorem eventually_higherSource_collisionScale10 (k : ℕ) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → ∀ p : ℕ,
      Real.log (p:ℝ) ≤ Real.log (higherSourceX k u:ℝ)/4 →
        p ≤ collisionScale 10 (higherSourceX k u) :=
  eventually_higherSourceX_property k α hα eventually_log_quarter_le_collisionScale10

theorem eventually_higherSource_testCount_le (k : ℕ) (α : ℝ) (hα : 0 < α) (N : ℕ) :
    ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u →
      (N:ℝ) ≤ Real.log (higherSourceX k u:ℝ) := by
  apply eventually_higherSourceX_property k α hα (P := fun X => (N:ℝ) ≤ Real.log (X:ℝ))
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (N:ℝ)

end Ostmann.Characters

end

end OAI
