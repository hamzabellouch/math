import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicPatchCap
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma slice_core_form_ge_baseline {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    E*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u E]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable u s).const_mul E)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hE.trans
      (unrestrictedFormBottom_le_trial S _ hx.normalized (mass_normalized _ hp)))

theorem atomic_outerKinetic_le {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {y : Space} (hy : y≠0)
    (hs : PartlySupported u (outIndexSet m k) (Metric.closedBall y (80*atomicCellScale y)))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    outerKinetic u≤form S u-E*mass u+
      (atomicCellScale y/2)*sliceExpectation u (fun s x => (atomicPatchCap S (u.coreSlice s x).normalized x y)^2)+
      (m:ℝ)^2/(2*atomicCellScale y)*mass u := by
  let a := atomicCellScale y
  have hapos : 0<a := atomicCellScale_pos hy
  have hbase := slice_core_form_ge_baseline S u ha hE
  have hcost : -((a/2)*sliceExpectation u (fun s x => (atomicPatchCap S (u.coreSlice s x).normalized x y)^2)+
      (m:ℝ)^2/(2*a)*mass u)≤
      sliceExpectation u (fun s x => pairPotential x-∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    rw [←sliceExpectation_number u ((m:ℝ)^2/(2*a))]
    unfold sliceExpectation
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro s _
    rw [←integral_const_mul,←integral_add ((atomicPatchCap_weight_integrable S hatom u s hy).const_mul (a/2))
      ((mass_coreSlice_integrable u s).mul_const _),←integral_neg]
    apply integral_mono_ae
      (((atomicPatchCap_weight_integrable S hatom u s hy).const_mul (a/2)).add
        ((mass_coreSlice_integrable u s).mul_const _)).neg
      (conditionalOutCost_weight_integrable S u s)
    filter_upwards [hs.recorded_positions s] with x hx
    by_cases hz : mass (u.coreSlice s x)=0
    · simp [hz]
    · have hfield : (∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i))≤
          (m:ℝ)*atomicPatchCap S (u.coreSlice s x).normalized x y := by
        calc
          _≤∑ _i : Fin m,atomicPatchCap S (u.coreSlice s x).normalized x y := by
            apply Finset.sum_le_sum
            intro i _
            apply coreField_le_atomicPatchCap S hatom _ x hy
            simpa only [Metric.mem_closedBall,dist_eq_norm] using hx hz i
          _=_ := by simp
      have hsq := sq_nonneg (a*atomicPatchCap S (u.coreSlice s x).normalized x y-(m:ℝ))
      have hyoung : (m:ℝ)*atomicPatchCap S (u.coreSlice s x).normalized x y≤
          (a/2)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2+(m:ℝ)^2/(2*a) := by
        apply (mul_le_mul_iff_right₀ (show 0<2*a by positivity)).mp
        have he : (m:ℝ)^2/(2*a)*(2*a)=(m:ℝ)^2 := div_mul_cancel₀ _ (by positivity)
        nlinarith
      have hh := mul_le_mul_of_nonneg_left (show -((a/2)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2+
          (m:ℝ)^2/(2*a))≤pairPotential x-∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i) by
          have hp : 0≤pairPotential x := by
            unfold pairPotential
            exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
              split_ifs <;> simp [coulombKernel]))
          linarith) (mass_nonneg (u.coreSlice s x))
      dsimp only [Pi.add_apply,Pi.neg_apply,Pi.mul_apply]
      nlinarith
  have hid := form_eq_conditionalOutCost S u
  unfold conditionalOutCost at hid
  change outerKinetic u≤form S u-E*mass u+(a/2)*_+(m:ℝ)^2/(2*a)*mass u
  linarith

end Coulomb
end

end
end

end OAI
