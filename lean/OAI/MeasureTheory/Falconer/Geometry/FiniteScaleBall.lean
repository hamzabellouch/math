import OAI.MeasureTheory.Falconer.Measures.ConditionalFrostman

namespace OAI

/-! # Finite-scale balls and the support of the actual rescaled laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

theorem finite_scale_ball_extend (μ : Measure X) {δ K s : ℝ}
    (hmass : μ univ ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hball : ∀ x : X, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : X, ∀ r : ℝ, δ ≤ r → μ (ball x r) ≤ ENNReal.ofReal (K*r^s) := by
  intro x r hr
  by_cases hr₁ : r ≤ 1
  · exact hball x r hr hr₁
  · have hp : 1 ≤ K*r^s := one_le_mul_of_one_le_of_one_le hK
      (Real.one_le_rpow (le_of_not_ge hr₁) hs)
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))

namespace Regularization
variable {d : ℕ}

theorem rescaled_cell_norm_bound (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖cellScaleMap P.length (Q.descendant P).center z‖ ≤ Real.sqrt d := by
  have hs : 0 < (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hdist := (Q.descendant P).dist_le hs.le hz ((Q.descendant P).center_mem hs)
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)]
  rw [dist_eq_norm] at hdist
  calc
    _ ≤ (2:ℝ)^P.length*(Real.sqrt d*(Q.descendant P).side) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = Real.sqrt d := by rw [Q.descendant_side,hQ]; field_simp

theorem rescaled_conditional_support (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) :
    ∀ᵐ z ∂Measure.map (cellScaleMap P.length (Q.descendant P).center)
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier), ‖z‖ ≤ Real.sqrt d := by
  rw [ae_map_iff (cellScaleMap_continuous _ _).measurable.aemeasurable
    (isClosed_le continuous_norm continuous_const).measurableSet]
  exact ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
    (fun z hz => rescaled_cell_norm_bound Q hQ P hz)

end Regularization
end Falconer

end OAI
