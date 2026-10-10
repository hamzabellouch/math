import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawObservable

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma potentialForm_coreSlice_joint_aestronglyMeasurable {m k : ℕ}
    (ψ : H1Vector (m+k)) (s : Spins m)
    (W : (Configuration m × Space) × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1)) (volume.prod volume) := by
  have hreg : ∀ᵐ z : Configuration m × Space ∂volume.prod volume, ψ.CoreSliceRegular s z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ψ.coreSliceRegular_ae s)
  apply AEStronglyMeasurable.congr _
    (show (fun z : Configuration m × Space => ∑ t : Spins k, ∫ v,
        W (z,v)*‖ψ.value (Fin.append s t) (joinConfiguration m k (z.1,v))‖^2) =ᵐ[volume.prod volume]
        (fun z => potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1)) from ?_)
  · apply Finset.aestronglyMeasurable_fun_sum
    intro t ht
    have hψ := ((ψ.value_L2 (Fin.append s t)).aestronglyMeasurable.comp_measurePreserving
      (joinConfiguration_measurePreserving m k)).norm.pow 2
    have hp : MeasurePreserving (fun z : (Configuration m × Space) × Configuration k =>
        ((z.1.1,z.2),z.1.2)) ((volume.prod volume).prod volume) ((volume.prod volume).prod volume) := by
      have h1 := measurePreserving_prodAssoc (volume : Measure (Configuration m))
        (volume : Measure Space) (volume : Measure (Configuration k))
      have h2 := (MeasurePreserving.id (volume : Measure (Configuration m))).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure Space)) (ν := (volume : Measure (Configuration k))))
      have h3 := (measurePreserving_prodAssoc (volume : Measure (Configuration m))
        (volume : Measure (Configuration k)) (volume : Measure Space)).symm MeasurableEquiv.prodAssoc
      exact h3.comp (h2.comp h1)
    have hl := (hψ.comp_fst (ν := (volume : Measure Space))).comp_measurePreserving hp
    exact (hW.aestronglyMeasurable.mul hl).integral_prod_right'
  · filter_upwards [hreg] with z hz
    simp only [potentialForm, ψ.coreSlice_value s hz]

lemma potentialForm_normalized_coreSlice_joint_aestronglyMeasurable {m k : ℕ}
    (ψ : H1Vector (m+k)) (s : Spins m)
    (W : (Configuration m × Space) × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      potentialForm (fun v => W (z,v)) (ψ.coreSlice s z.1).normalized) (volume.prod volume) := by
  simp only [potentialForm_normalized_eq]
  exact ((mass_coreSlice_integrable ψ s).aestronglyMeasurable.comp_fst).inv₀.mul
    (potentialForm_coreSlice_joint_aestronglyMeasurable ψ s W hW)

lemma restrictedOutPotential_joint_measurable {m : ℕ} {A : Set Space} (hA : MeasurableSet A) :
    Measurable (fun z : Configuration m × Space => restrictedOutPotential z.1 A z.2) := by
  apply Finset.measurable_fun_sum
  intro i hi
  apply Measurable.ite (hA.preimage ((continuous_position i).measurable.comp measurable_fst)) _ measurable_const
  simp only [coulombKernel]
  exact (((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv

lemma restrictedCorePotential_normalized_slice_joint {m k : ℕ} (u : H1Vector (m+k))
    (s : Spins m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      restrictedCorePotential (u.coreSlice s z.1).normalized A z.2) (volume.prod volume) := by
  have hW : Measurable (fun z : (Configuration m × Space) × Configuration k =>
      restrictedOutPotential z.2 A z.1.2) :=
    (restrictedOutPotential_joint_measurable hA).comp (measurable_snd.prodMk measurable_fst.snd)
  have H := potentialForm_normalized_coreSlice_joint_aestronglyMeasurable u s _ hW
  simpa only [potentialForm_restrictedOutPotential _ hA] using H

lemma recordedFarField_normalized_slice_joint {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun z : Configuration m × Space =>
      recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) (volume.prod volume) := by
  exact ((attraction_measurable S).comp measurable_snd).aestronglyMeasurable.sub
    (restrictedCorePotential_normalized_slice_joint u s hA) |>.sub
    (restrictedOutPotential_joint_measurable hA).aestronglyMeasurable

lemma farSquare_mass_ballCloud_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun z : Configuration m × Space => mass (u.coreSlice s z.1)*
      (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0)^2*
      ballCloud y a 1 z.2) (volume.prod volume) := by
  let K := (totalCharge S/a)^2
  have hm := (mass_coreSlice_integrable u s).aestronglyMeasurable.comp_fst (ν := (volume : Measure Space))
  have hf := ((recordedFarField_normalized_slice_joint S u s hA).sup
    (aestronglyMeasurable_const (b:=(0:ℝ)))).pow 2
  have hb : Measurable (fun z : Configuration m × Space => ballCloud y a 1 z.2) :=
    (ballCloud_measurable a 1 y).comp measurable_snd
  apply (((mass_coreSlice_integrable u s).mul_prod (ballCloud_integrable a 1 y)).const_mul K).mono'
    ((hm.mul hf).mul hb.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖mass (u.coreSlice s z.1)*
    (max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0)^2*ballCloud y a 1 z.2‖ ≤ _
  have hball : 0 ≤ ballCloud y a 1 z.2 := uniformBall_nonneg ha zero_le_one (z.2-y)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mass_nonneg _) (sq_nonneg _)) hball)]
  by_cases hz : z.2-y ∈ Metric.ball (0:Space) a
  · have hdist : ‖z.2-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hsep (j : Fin J) : a ≤ ‖z.2-S.position j‖ := by
      have ht : ‖S.position j-y‖ ≤ ‖S.position j-z.2‖+‖z.2-y‖ := by
        simpa only [dist_eq_norm] using dist_triangle (S.position j) z.2 y
      rw [norm_sub_rev (S.position j) z.2] at ht
      linarith [hnuc j]
    have hP : max (recordedFarField S (u.coreSlice s z.1).normalized z.1 A z.2) 0 ≤ totalCharge S/a :=
      (max_le (recordedFarField_le_attraction S _ _ A z.2) (attraction_nonneg S z.2)).trans
        (attraction_le_totalCharge_div S ha z.2 hsep)
    have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_max_right _ _) hP 2) (mass_nonneg (u.coreSlice s z.1))) hball
    dsimp [K]
    nlinarith
  · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]

theorem sliceExpectation_farSquare_ballCloud {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    sliceExpectation u (fun s x => ∫ v,
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2*ballCloud y a 1 v) =
    ∫ v, (sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2))*ballCloud y a 1 v := by
  unfold sliceExpectation
  simp only [←integral_const_mul,Finset.sum_mul,←integral_mul_const]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    have H := integral_integral_swap (f := fun x v => mass (u.coreSlice s x)*
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2*ballCloud y a 1 v)
      (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc)
    simpa only [mul_assoc] using H
  · intro s hs
    exact (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc).integral_prod_right

end Coulomb
end

end
end

end OAI
