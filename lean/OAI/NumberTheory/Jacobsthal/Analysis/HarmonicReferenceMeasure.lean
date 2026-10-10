import OAI.NumberTheory.Jacobsthal.Estimates.WeightedMonotoneBound
import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HarmonicReferenceMeasure

open _root_.MeasureTheory _root_.Set
open ErdosMonotoneQuadrature ErdosPrimeInputs.PrimeEndpoints

noncomputable def referenceMeasure (u v : ℝ) : Measure ℝ :=
  reciprocalMeasure (volume.restrict (Icc u v)) u

theorem referenceMeasure_finite {u v : ℝ} (hu : 0 < u) : IsFiniteMeasure (referenceMeasure u v) :=
  reciprocalMeasure_finite _ hu

theorem referenceMeasure_real {u v : ℝ} (hu : 0 < u) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc u v) :
    (referenceMeasure u v).real J=∫ x in J,(1:ℝ)/x := by
  rw [referenceMeasure,reciprocalMeasure_real _ hu hJ,Measure.restrict_restrict hJ,
    inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  rw [reciprocalWeight_eq (hsub hx).1,one_div]

theorem referenceMeasure_weightedIntegral {u v : ℝ} (hu : 0 < u) (g : ℝ → ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ Icc u v) :
    (∫ x in J,g x/x ∂referenceMeasure u v)=∫ x in J,g x/x^2 := by
  rw [referenceMeasure,reciprocalMeasure_integral _ hu _ hJ,Measure.restrict_restrict hJ,
    inter_eq_left.mpr hsub]
  apply setIntegral_congr_fun hJ
  intro x hx
  dsimp only
  rw [reciprocalWeight_eq (hsub hx).1]
  simp only [div_eq_mul_inv,pow_two,mul_inv_rev]
  ring

theorem intervalGuard_subset {u v a b : ℝ} (hua : u ≤ a) (hbv : b ≤ v) (lc rc : Bool) :
    {x | intervalGuard lc rc a b x} ⊆ Icc u v := by
  intro x hx
  have ha : a ≤ x := by cases lc <;> simp only [intervalGuard,ite_true,Bool.false_eq_true,ite_false] at hx <;> linarith [hx.1]
  have hb : x ≤ b := by cases rc <;> simp only [intervalGuard,ite_true,Bool.false_eq_true,ite_false] at hx <;> linarith [hx.2]
  exact ⟨hua.trans ha,hb.trans hbv⟩

theorem intervalGuard_measurable (lc rc : Bool) (a b : ℝ) : MeasurableSet {x | intervalGuard lc rc a b x} := by
  cases lc <;> cases rc <;> simp only [intervalGuard,ite_true,Bool.false_eq_true,ite_false] <;> measurability

theorem referenceMeasure_interval {u v a b : ℝ} (hu : 0 < u) (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v)
    (lc rc : Bool) :
    (referenceMeasure u v).real {x | intervalGuard lc rc a b x}=Real.log b-Real.log a := by
  rw [referenceMeasure_real hu (intervalGuard_measurable lc rc a b) (intervalGuard_subset hua hbv lc rc)]
  have ha : 0 < a := hu.trans_le hua
  have hb : 0 < b := ha.trans_le hab
  have hbase : (∫ x in Ioc a b,(1:ℝ)/x)=Real.log b-Real.log a := by
    rw [← intervalIntegral.integral_of_le hab,integral_one_div_of_pos ha hb,Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  cases lc <;> cases rc
  · change (∫ x in Ioo a b,(1:ℝ)/x)=_
    rw [← integral_Ioc_eq_integral_Ioo]
    exact hbase
  · exact hbase
  · change (∫ x in Ico a b,(1:ℝ)/x)=_
    rw [integral_Ico_eq_integral_Ioc]
    exact hbase
  · change (∫ x in Icc a b,(1:ℝ)/x)=_
    rw [integral_Icc_eq_integral_Ioc]
    exact hbase

end NumberTheoryLean.HarmonicReferenceMeasure

end

end Erdos970

end OAI
