import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Comparison
variable {U X : Type*} [MeasurableSpace U] [MeasurableSpace X]

lemma failure_large_of_success_small (P : Measure X) [IsProbabilityMeasure P]
    (S : Set X) (hS : MeasurableSet S) {a b : ℝ≥0∞} (hab : a+b≤1)
    (hsmall : P S<a) : b≤P Sᶜ := by
  by_contra! hb
  have hsum : P S+P Sᶜ=1 := by simpa using measure_add_measure_compl (μ:=P) hS
  have hlt := ENNReal.add_lt_add hsmall hb
  rw [hsum] at hlt
  exact (not_lt_of_ge hab) hlt

lemma bad_target_mass (μ : Measure U) (κ : Kernel U X) [IsMarkovKernel κ]
    (S : Set X) (hS : MeasurableSet S) {a b : ℝ≥0∞} (hab : a+b≤1) :
    b*μ {u | κ u S<a}≤∫⁻u,κ u Sᶜ ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral (κ.measurable_coe hS.compl) b)
  apply mul_le_mul_right
  apply measure_mono
  exact fun u hu ↦ failure_large_of_success_small (κ u) S hS hab hu

lemma good_target_mass_of_failure (μ : Measure U) [IsProbabilityMeasure μ]
    (κ : Kernel U X) [IsMarkovKernel κ] (S : Set X) (hS : MeasurableSet S)
    (hf : (∫⁻u,κ u Sᶜ ∂μ)≤ENNReal.ofReal (1/1000:ℝ)) :
    ENNReal.ofReal (99/100:ℝ)≤μ {u | ENNReal.ofReal (9/10:ℝ)≤κ u S} := by
  have hab : ENNReal.ofReal (9/10:ℝ)+ENNReal.ofReal (1/10:ℝ)≤1 := by
    rw [←ENNReal.ofReal_add (by norm_num : (0:ℝ)≤9/10) (by norm_num : (0:ℝ)≤1/10)]
    norm_num
  have h := (bad_target_mass μ κ S hS hab).trans hf
  have hbad : μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}≤ENNReal.ofReal (1/100:ℝ) := by
    calc
      _ = ENNReal.ofReal 10*(ENNReal.ofReal (1/10:ℝ)*μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}) := by
        rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]; norm_num
      _ ≤ ENNReal.ofReal 10*ENNReal.ofReal (1/1000:ℝ) := mul_le_mul_right h _
      _ = _ := by rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]; norm_num
  have hT : MeasurableSet {u | ENNReal.ofReal (9/10:ℝ)≤κ u S} := measurableSet_le measurable_const (κ.measurable_coe hS)
  have he : μ {u | ENNReal.ofReal (9/10:ℝ)≤κ u S}+μ {u | κ u S<ENNReal.ofReal (9/10:ℝ)}=1 := by
    simpa only [Set.compl_ofPred,not_le,measure_univ] using measure_add_measure_compl (μ:=μ) hT
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
  have her := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at her
  have hbadr := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbad
  norm_num at her hbadr ⊢
  linarith

lemma seven_target_count {m : ℕ} (score : Fin m→Fin 7→ℝ)
    (h0 : ∀i w,0 ≤ score i w)
    (hscore : ∀w, (∑i,score i w)≤(m:ℝ)/70000) :
    ((Finset.univ.filter (fun i ↦ ∃w, (1/1000:ℝ)<score i w)).card:ℝ)≤(m:ℝ)/10 := by
  classical
  let bad : Finset (Fin m) := Finset.univ.filter (fun i ↦ ∃w, (1/1000:ℝ)<score i w)
  have hlower : (bad.card:ℝ)*(1/1000)≤∑i,∑w,score i w := by
    calc
      _ = ∑_i∈bad,(1/1000:ℝ) := by simp
      _ ≤ ∑i∈bad,∑w,score i w := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨w,hw⟩ := (Finset.mem_filter.mp hi).2
        exact hw.le.trans (Finset.single_le_sum (fun j _ ↦ h0 i j) (Finset.mem_univ w))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ Finset.sum_nonneg (fun w _ ↦ h0 i w))
  have hupper : (∑i,∑w,score i w)≤(m:ℝ)/10000 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑_w : Fin 7,(m:ℝ)/70000 := Finset.sum_le_sum (fun w _ ↦ hscore w)
      _ = _ := by simp; ring
  change (bad.card:ℝ)≤(m:ℝ)/10
  linarith

end HardSphere.Comparison

end
end

end

end OAI
