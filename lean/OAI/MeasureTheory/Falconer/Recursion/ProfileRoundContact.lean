import OAI.MeasureTheory.Falconer.Recursion.ProfileContactStability
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Contact intervals tolerate the rounding of their initial dyadic depth -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

theorem profile_contact_move_left {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K f (Icc 0 1)) {a A B s E ε : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hAB : A ≤ B) (hB : B ≤ 1)
    (hs : 0 ≤ s) (hclose : A-a ≤ ε)
    (hcontact : ∀ w ∈ Icc A B, s*(w-A)-E ≤ f w-f A) :
    ∀ w ∈ Icc a B, s*(w-a)-E-((K:ℝ)+s)*ε ≤ f w-f a := by
  have hA0 : 0 ≤ A := ha.trans haA
  have ha1 : a ≤ 1 := (haA.trans hAB).trans hB
  have hA1 : A ≤ 1 := hAB.trans hB
  have hfa : |f A-f a| ≤ (K:ℝ)*(A-a) := by
    simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr haA)] using
      hLip.dist_le_mul A ⟨hA0,hA1⟩ a ⟨ha,ha1⟩
  have hK := K.coe_nonneg
  intro w hw
  by_cases hAw : A ≤ w
  · have hh := hcontact w ⟨hAw,hw.2⟩
    have he := mul_le_mul_of_nonneg_left hclose (add_nonneg hK hs)
    nlinarith [neg_abs_le (f A-f a)]
  · have hwA : w ≤ A := (lt_of_not_ge hAw).le
    have hw1 : w ≤ 1 := hw.2.trans hB
    have hfw : |f w-f a| ≤ (K:ℝ)*(w-a) := by
      simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hw.1)] using
        hLip.dist_le_mul w ⟨ha.trans hw.1,hw1⟩ a ⟨ha,ha1⟩
    have hE : 0 ≤ E := by
      have hh := hcontact A ⟨le_rfl,hAB⟩
      simp only [sub_self,mul_zero,zero_sub] at hh
      linarith
    have hwe : w-a ≤ ε := (sub_le_sub_right hwA a).trans hclose
    nlinarith [neg_abs_le (f w-f a),mul_le_mul_of_nonneg_left hwe (add_nonneg hK hs)]

theorem floor_depth_ratio_tendsto {A : ℝ} (hA : 0 ≤ A) :
    Tendsto (fun N : ℕ => (Nat.floor (A*(N:ℝ)):ℝ)/(N:ℝ)) atTop (𝓝 A) :=
  (tendsto_nat_floor_mul_div_atTop hA).comp tendsto_natCast_atTop_atTop

end Falconer

end OAI
