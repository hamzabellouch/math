import OAI.NumberTheory.Jacobsthal.Probability.TwoSidedThresholdKernel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdHazard
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels
open TwoSidedThresholdGeometry TwoSidedThresholdKernel CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

noncomputable def thickHazard (R d e : ℝ) : State → ℝ
  | .inl _ => 0
  | .inr s => if 3 ≤ R then
      (oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R (d/R+e))).toReal else 0

theorem thickHazard_exposure (s : State) {R d e : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (he : 0 ≤ e) :
    thickHazard R d e s ≤ thickConstant*d*(if 3 ≤ R ∧ stateRatio s ≤ 6 then 1/R else 0)+thickConstant*e := by
  have hC := thickConstant_pos
  cases s with
  | inl s =>
    change 0 ≤ _
    split_ifs <;> positivity
  | inr s =>
    by_cases hR3 : 3 ≤ R
    · by_cases hs : s.1 ≤ 6
      · simp only [thickHazard,ite_eq_left hR3]
        split_ifs with hguard
        · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
            (oddToEven_thick_bound s hR3 (show 0 ≤ d/R+e by positivity))
          rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ thickConstant*(d/R+e))] at hh
          calc
            _ ≤ thickConstant*(d/R+e) := hh
            _ = _ := by ring
        · exact (hguard ⟨hR3,hs⟩).elim
      · rw [thickHazard,ite_eq_left hR3,oddToEven_thick_zero_high_parent s (lt_of_not_ge hs)]
        simp only [ENNReal.toReal_zero,stateRatio,Sum.elim_inr,hs,and_false,ite_false,mul_zero,zero_add]
        positivity
    · rw [thickHazard,ite_eq_right hR3]
      simp only [hR3,false_and,ite_false,mul_zero,zero_add]
      positivity

theorem canonical_total_thick_hazard (v : ℝ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,
      (∑ j : Fin (N+1),thickHazard (gapValue v (coordinate N h j)) d e (coordinate N h j).1) ≤
        thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
  filter_upwards [canonical_exposure_bound v (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)≤6) s N] with h hh
  have hsum : (∑ j : Fin (N+1),thickHazard (gapValue v (coordinate N h j)) d e (coordinate N h j).1) ≤
      thickConstant*d*pathExposure v 3 6 N h+((N:ℝ)+1)*(thickConstant*e) := by
    calc
      _ ≤ ∑ j : Fin (N+1),(thickConstant*d*(if 3 ≤ gapValue v (coordinate N h j) ∧
          stateRatio (coordinate N h j).1 ≤ 6 then 1/gapValue v (coordinate N h j) else 0)+thickConstant*e) := by
        apply Finset.sum_le_sum
        intro j _
        exact thickHazard_exposure _ (Real.exp_pos _) hd he
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; simp [pathExposure,Nat.cast_add,Nat.cast_one]
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg thickConstant_pos.le hd)
  calc
    _ ≤ thickConstant*d*((6+2)/3)+((N:ℝ)+1)*(thickConstant*e) := by linarith
    _ = _ := by ring
end NumberTheoryLean.TwoSidedThresholdHazard

end

end Erdos970

end OAI
