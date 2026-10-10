import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FieldSubmean
import OAI.Analysis.CoulombRadii.FieldAnalysis.RestrictedField

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma restrictedOutPotential_measurable {m : ℕ} (x : Configuration m) (A : Set Space) :
    Measurable (restrictedOutPotential x A) := by
  apply Finset.measurable_fun_sum
  intro i hi
  by_cases h : position x i ∈ A
  · simp only [ite_eq_left h, coulombKernel]
    fun_prop
  · simp only [ite_eq_right h]
    exact measurable_const

lemma restrictedOutPotential_ballCloud_integrable {m : ℕ} (x : Configuration m) (A : Set Space)
    {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => restrictedOutPotential x A z*ballCloud y a 1 z) := by
  simp only [restrictedOutPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i hi
  by_cases h : position x i ∈ A
  · simpa only [ite_eq_left h] using coulomb_convolution_integrable (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (fun z => uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => uniformBall_le ha zero_le_one (z-y)) ha (position x i)
  · simp only [ite_eq_right h,zero_mul]
    exact integrable_zero _ _ _

lemma restrictedOutPotential_ballCloud {m : ℕ} (x : Configuration m) (A : Set Space)
    {a : ℝ} (ha : 0 < a) (y : Space) (hsep : ∀ v ∈ A, a ≤ ‖v-y‖) :
    (∫ z, restrictedOutPotential x A z*ballCloud y a 1 z)=restrictedOutPotential x A y := by
  have hi (i : Fin m) : Integrable (fun z =>
      (if position x i ∈ A then coulombKernel (position x i-z) else 0)*ballCloud y a 1 z) := by
    by_cases h : position x i ∈ A
    · simpa only [ite_eq_left h] using coulomb_convolution_integrable (ballCloud_integrable a 1 y)
        (ballCloud_measurable a 1 y) (fun z => uniformBall_nonneg ha zero_le_one (z-y))
        (fun z => uniformBall_le ha zero_le_one (z-y)) ha (position x i)
    · simp only [ite_eq_right h,zero_mul]
      exact integrable_zero _ _ _
  unfold restrictedOutPotential
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi'
  by_cases h : position x i ∈ A
  · simp only [ite_eq_left h]
    simpa only [one_mul] using ballCloud_coulomb ha zero_le_one y (position x i) (hsep _ h)
  · simp [h]

lemma recordedFarField_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) :
    AEStronglyMeasurable (recordedFarField S u x A) volume :=
  ((attraction_measurable S).aestronglyMeasurable.sub (restrictedCorePotential_aestronglyMeasurable u hA)).sub
    (restrictedOutPotential_measurable x A).aestronglyMeasurable

lemma attraction_ballCloud_integrable {J : ℕ} (S : Nuclei J) {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => attraction S z*ballCloud y a 1 z) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j hj
  have H := (coulomb_convolution_integrable (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => uniformBall_nonneg ha zero_le_one (z-y))
    (fun z => uniformBall_le ha zero_le_one (z-y)) ha (S.position j)).const_mul (S.charge j)
  exact H.congr (Eventually.of_forall (fun z => by dsimp only; rw [coulombKernel_sub_comm]; ring))

lemma recordedFarField_ballCloud_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (y : Space) :
    Integrable (fun z => recordedFarField S u x A z*ballCloud y a 1 z) := by
  apply (((attraction_ballCloud_integrable S ha y).sub
    (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y))).sub
    (restrictedOutPotential_ballCloud_integrable x A ha y)).congr
  exact Eventually.of_forall (fun z => by dsimp only [Pi.sub_apply,recordedFarField]; ring)

lemma recordedFarField_ballCloud {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    (∫ z, recordedFarField S u x A z*ballCloud y a 1 z)=recordedFarField S u x A y := by
  simp only [recordedFarField,sub_mul]
  have hsub : Integrable (fun z => attraction S z*ballCloud y a 1 z-
      restrictedCorePotential u A z*ballCloud y a 1 z) := by
    exact (attraction_ballCloud_integrable S ha y).sub
      (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y))
  rw [integral_sub hsub (restrictedOutPotential_ballCloud_integrable x A ha y),
    integral_sub (attraction_ballCloud_integrable S ha y)
      (restrictedCorePotential_mul_integrable u hA _ (ballCloud_integrable a 1 y)),
    attraction_ballCloud S ha zero_le_one y hnuc,
    restrictedCorePotential_ballCloud u hA ha zero_le_one y hcore,
    restrictedOutPotential_ballCloud x A ha y hcore,one_mul,one_mul]

lemma positive_ballCloud_integrable {a : ℝ} (ha : 0 < a) (y : Space) (f : Space → ℝ)
    (hf : Integrable (fun z => f z*ballCloud y a 1 z)) :
    Integrable (fun z => max (f z) 0*ballCloud y a 1 z) := by
  apply (hf.sup (integrable_zero _ _ _)).congr
  filter_upwards [] with z
  change max (f z*ballCloud y a 1 z) 0 = _
  symm
  simpa only [zero_mul, ballCloud] using max_mul_of_nonneg (f z) 0 (uniformBall_nonneg ha zero_le_one (z-y))

lemma positive_square_ballCloud_integrable {J : ℕ} (S : Nuclei J) (f : Space → ℝ)
    (hm : AEStronglyMeasurable f volume) (hbound : ∀ z, f z ≤ attraction S z)
    {a : ℝ} (ha : 0 < a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun z => (max (f z) 0)^2*ballCloud y a 1 z) := by
  have hp : AEStronglyMeasurable (fun z => (max (f z) 0)^2) volume :=
    (hm.sup aestronglyMeasurable_const).pow 2
  apply ((ballCloud_integrable a 1 y).const_mul ((totalCharge S/a)^2)).mono'
    (hp.mul (ballCloud_measurable a 1 y).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(max (f z) 0)^2*ballCloud y a 1 z‖ ≤ _
  have hball : 0 ≤ ballCloud y a 1 z := uniformBall_nonneg ha zero_le_one (z-y)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hball)]
  by_cases hz : z-y ∈ Metric.ball (0:Space) a
  · have hdist : ‖z-y‖ < a := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hsep (j : Fin J) : a ≤ ‖z-S.position j‖ := by
      have ht : ‖S.position j-y‖ ≤ ‖S.position j-z‖+‖z-y‖ := by
        simpa only [dist_eq_norm] using dist_triangle (S.position j) z y
      rw [norm_sub_rev (S.position j) z] at ht
      linarith [hnuc j]
    have hP : max (f z) 0 ≤ totalCharge S/a :=
      (max_le (hbound z) (attraction_nonneg S z)).trans (attraction_le_totalCharge_div S ha z hsep)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_right _ _) hP 2)
      (uniformBall_nonneg ha zero_le_one (z-y))
  · simp only [ballCloud,uniformBall,indicator_of_notMem hz,mul_zero,le_refl]

theorem recordedFarField_positive_submean_square {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) {a : ℝ} (ha : 0 < a) (z w : Space)
    (hw : ‖w-z‖ ≤ a) (hcore : ∀ v ∈ A, 4*a ≤ ‖v-z‖)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    (max (recordedFarField S u x A w) 0)^2 ≤
      8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v) := by
  have hsep (v : Space) (hv : 4*a ≤ ‖v-z‖) : 2*a ≤ ‖v-w‖ := by
    have ht : ‖v-z‖ ≤ ‖v-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle v w z
    linarith
  let f := recordedFarField S u x A
  have hci := recordedFarField_ballCloud_integrable S u x hA ha w
  have hpi := positive_ballCloud_integrable ha w f hci
  have hmeas := recordedFarField_aestronglyMeasurable S u x hA
  have hbound := recordedFarField_le_attraction S u x A
  have hsi := positive_square_ballCloud_integrable S f hmeas hbound ha w (fun j => hsep _ (hnuc j))
  have hsz := positive_square_ballCloud_integrable S f hmeas hbound (by linarith : 0 < 2*a) z
    (fun j => by linarith [hnuc j])
  have hmean : f w=∫ v, f v*ballCloud w a 1 v :=
    (recordedFarField_ballCloud S u x hA ha w
      (fun v hv => le_trans (by linarith) (hsep _ (hcore v hv)))
      (fun j => le_trans (by linarith) (hsep _ (hnuc j)))).symm
  have hpmean : max (f w) 0 ≤ ∫ v, max (f v) 0*ballCloud w a 1 v := by
    apply max_le
    · rw [hmean]
      exact integral_mono hci hpi (fun v => mul_le_mul_of_nonneg_right (le_max_left _ _)
        (uniformBall_nonneg ha zero_le_one (v-w)))
    · exact integral_nonneg (fun v => mul_nonneg (le_max_right _ _) (uniformBall_nonneg ha zero_le_one (v-w)))
  calc
    _ ≤ (∫ v, max (f v) 0*ballCloud w a 1 v)^2 := pow_le_pow_left₀ (le_max_right _ _) hpmean 2
    _ ≤ ∫ v, (max (f v) 0)^2*ballCloud w a 1 v :=
      square_weighted_mean_le volume _ _ (ballCloud_integrable a 1 w)
        (fun v => uniformBall_nonneg ha zero_le_one (v-w)) (ballCloud_mass ha 1 w) hpi hsi
    _ ≤ _ := by
      rw [← integral_const_mul]
      apply integral_mono hsi (hsz.const_mul 8)
      intro v
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (ballCloud_nested_le ha z w v hw)
        (sq_nonneg (max (f v) 0))

lemma restrictedOutPotential_le {m : ℕ} (x : Configuration m) (A : Set Space)
    {r : ℝ} (hr : 0 < r) (y : Space) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) :
    restrictedOutPotential x A y ≤ (m:ℝ)/r := by
  calc
    _ ≤ ∑ _i : Fin m, 1/r := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : position x i ∈ A
      · simp only [ite_eq_left h, coulombKernel]
        simpa only [one_div] using one_div_le_one_div_of_le hr (hsep _ h)
      · simp only [ite_eq_right h]
        positivity
    _ = _ := by simp; ring

theorem coreField_le_local_far_cap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {a : ℝ} (ha : 0 < a) (z w : Space)
    (hw : ‖w-z‖ ≤ a) (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    coreScreenedField S u w ≤
      Real.sqrt (8*(∫ v, (max (recordedFarField S u x {v | 4*a ≤ ‖v-z‖} v) 0)^2*ballCloud z (2*a) 1 v))+
      (m:ℝ)/(3*a) := by
  let A : Set Space := {v | 4*a ≤ ‖v-z‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  have H := recordedFarField_positive_submean_square S u x hA ha z w hw (fun _ h => h) hnuc
  have hpos : 0 ≤ 8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v) := by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun v => mul_nonneg (sq_nonneg _) (uniformBall_nonneg (by linarith) zero_le_one (v-z)))
  have HB := (Real.le_sqrt (le_max_right _ _) hpos).2 H
  have HO : restrictedOutPotential x A w ≤ (m:ℝ)/(3*a) := by
    apply restrictedOutPotential_le x A (by positivity) w
    intro v hv
    have ht : ‖v-z‖ ≤ ‖v-w‖+‖w-z‖ := by simpa only [dist_eq_norm] using dist_triangle v w z
    change 4*a ≤ ‖v-z‖ at hv
    linarith
  have HC := coreField_le_far_addback S u x hA w
  have HE := le_max_left (recordedFarField S u x A w) 0
  change coreScreenedField S u w ≤ Real.sqrt (8*(∫ v, (max (recordedFarField S u x A v) 0)^2*ballCloud z (2*a) 1 v))+(m:ℝ)/(3*a)
  linarith

end Coulomb
end

end
end

end OAI
