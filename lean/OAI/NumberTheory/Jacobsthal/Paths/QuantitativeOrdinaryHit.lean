import OAI.NumberTheory.Jacobsthal.Probability.MarkedCostHitReduction

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelPotential

lemma absoluteBeginningWindow_mass_cost (z : RegCost) (v H : ℝ) :
    potential (beginningWindow 0 v H) (beginningBelow 0 v) z univ =
      potential (clockWindow v H) (clockBelow v) (beginningCost z) univ := by
  have he := costProjection_potential (relativeBeginningCost_measurable 0)
    (beginningBelow_projection 0 v) (beginningWindow_projection 0 v H) z
  apply_fun (fun μ : Measure ℝ => μ univ) at he
  rw [Measure.map_apply (relativeBeginningCost_measurable 0) MeasurableSet.univ,preimage_univ] at he
  simpa only [relativeBeginningCost,sub_zero] using he

lemma markedWindowSuccess_le_cost_hit (z : RegCost) (v H : ℝ) :
    markedWindowSuccess v H z ≤ costCurrentHit v H (beginningCost z) univ := by
  rw [markedWindowSuccess]
  by_cases hz : beginningCost z < v
  · rw [ite_eq_left hz,absoluteBeginningWindow_mass_cost]
    have hsub : Iio v ⊆ (Icc v (v+H))ᶜ := by
      intro x hx hs
      exact (not_lt_of_ge hs.1) hx
    exact restricted_crossing_le_current_hit markedClockKernel
      (S := Icc v (v+H)) (T := Iio v) measurableSet_Icc measurableSet_Iio hsub _ hz
  · rw [ite_eq_right hz]
    split_ifs with hin
    · exact currentHit_inside markedClockKernel (S := Icc v (v+H)) measurableSet_Icc
        (beginningCost z) ⟨le_of_not_gt hz,hin⟩
    · exact zero_le

theorem initialMarkedWindowSuccess_le_ordinaryHit (s : EvenState) (v H : ℝ) :
    initialMarkedWindowSuccess s v H ≤ ordinaryInitialHitMass s v H := by
  rw [ordinaryInitialHit_cost_law,initialMarkedWindowSuccess]
  calc
    _ ≤ ∫⁻ z, costCurrentHit v H (beginningCost z) univ ∂initialBeginningReg s :=
      lintegral_mono (fun z => markedWindowSuccess_le_cost_hit z v H)
    _ = ∫⁻ T, costCurrentHit v H T univ ∂(initialBeginningReg s).map beginningCost := by
      rw [lintegral_map ((costCurrentHit v H).measurable_coe MeasurableSet.univ) beginningCost_measurable]
    _ = _ := by rw [initialBeginningReg_cost_law]

theorem ordinaryInitialHit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S → ∀ v H : ℝ,
      0 ≤ H → 1-ordinaryInitialHitMass s v H ≤
        ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,hBound⟩ := initialMarkedWindow_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro s hs v H hH
  apply tsub_le_iff_right.mpr
  have he : 1 ≤ ordinaryInitialHitMass s v H+
      ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
    calc
      1 = initialMarkedWindowSuccess s v H+initialMarkedWindowFailure s v H :=
        (initialMarkedWindow_partition s v H hH).symm
      _ ≤ _ := add_le_add (initialMarkedWindowSuccess_le_ordinaryHit s v H) (hBound s hs v H hH)
  simpa only [add_comm] using he

theorem moving_ordinary_marked_hit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-ordinaryInitialHitMass s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤ ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_marked_window_capture heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr s hs0 hs1
  have hOld := hw.2 r hr s hs0 hs1
  have hWidth : 0 ≤ Real.log (rho/10) := Real.log_nonneg (by linarith)
  apply tsub_le_iff_right.mpr
  have he : 1 ≤ ordinaryInitialHitMass s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
      ENNReal.ofReal eps := by
    calc
      1 = initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
          initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) :=
        (initialMarkedWindow_partition _ _ _ hWidth).symm
      _ ≤ _ := add_le_add (initialMarkedWindowSuccess_le_ordinaryHit _ _ _) hOld.1
  simpa only [add_comm] using he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
