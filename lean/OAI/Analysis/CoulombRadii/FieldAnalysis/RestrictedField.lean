import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.UniformBall

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def restrictedCorePotential {k : ℕ} (u : H1Vector k) (A : Set Space) (y : Space) : ℝ :=
  ∑ s : Spins k, ∑ i : Fin k, ∫ x : Configuration k,
    if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0

lemma restrictedCore_integrable {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hA : MeasurableSet A) (s : Spins k) (i : Fin k) (y : Space) :
    Integrable (fun x => if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0) := by
  exact ((u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1).indicator
    (hA.preimage (continuous_position i).measurable)

lemma restrictedCorePotential_nonneg {k : ℕ} (u : H1Vector k) (A : Set Space) (y : Space) :
    0 ≤ restrictedCorePotential u A y := by
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.sum_nonneg
  intro i hi
  apply integral_nonneg
  intro x
  dsimp only [Pi.zero_apply]
  split_ifs <;> first | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _) | exact le_rfl

lemma restrictedCorePotential_le {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) : restrictedCorePotential u A y ≤ coreCoulombPotential u y := by
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro i hi
  apply integral_mono (restrictedCore_integrable u hA s i y)
    (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  intro x
  dsimp only [Pi.zero_apply]
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _)

lemma restrictedCorePotential_mono {k : ℕ} (u : H1Vector k) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) (y : Space) :
    restrictedCorePotential u A y ≤ restrictedCorePotential u B y := by
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro i hi
  apply integral_mono (restrictedCore_integrable u hA s i y) (restrictedCore_integrable u hB s i y)
  intro x
  by_cases h : position x i ∈ A
  · simp [h,hAB h]
  · simp only [ite_eq_right h]
    split_ifs <;> first | exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (sq_nonneg _) | exact le_rfl

lemma restrictedCorePotential_eq {k : ℕ} (u : H1Vector k) {A : Set Space}
    (hu : SpatiallySupported u A) (y : Space) : restrictedCorePotential u A y=coreCoulombPotential u y := by
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases h : position x i ∈ A
  · simp [h]
  · have hz : u.value s x=0 := hx (fun hh => h (hh i))
    simp [h,hz]

lemma restrictedCorePotential_aestronglyMeasurable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) : AEStronglyMeasurable (restrictedCorePotential u A) volume := by
  unfold restrictedCorePotential
  apply Finset.aestronglyMeasurable_fun_sum
  intro s hs
  apply Finset.aestronglyMeasurable_fun_sum
  intro i hi
  have hK : AEStronglyMeasurable (fun z : Configuration k × Space =>
      coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2) (volume.prod volume) :=
    ((((continuous_position i).measurable.comp measurable_fst).sub measurable_snd).norm.inv.aestronglyMeasurable).mul
      ((u.value_L2 s).aestronglyMeasurable.norm.pow 2).comp_fst
  have H := hK.indicator (hA.preimage ((continuous_position i).measurable.comp measurable_fst))
  exact H.prod_swap.integral_prod_right'

lemma restrictedCore_density_prod_integrable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (s : Spins k) (i : Fin k)
    (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun z : Configuration k × Space =>
      if position z.1 i ∈ A then coulombKernel (position z.1 i-z.2)*‖u.value s z.1‖^2*d z.2 else 0)
      (volume.prod volume) := by
  exact (u.coulomb_density_prod_integrable s i d hd).indicator
    (hA.preimage ((continuous_position i).measurable.comp measurable_fst))

lemma restrictedCorePotential_mul_integrable {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (d : Space → ℝ) (hd : Integrable d) :
    Integrable (fun y => restrictedCorePotential u A y*d y) := by
  simp only [restrictedCorePotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro s hs
  apply integrable_finsetSum
  intro i hi
  have H := (restrictedCore_density_prod_integrable u hA s i d hd).integral_prod_right
  apply H.congr
  filter_upwards [] with y
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  split_ifs <;> simp

lemma restrictedCorePotential_fubini {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) (d : Space → ℝ) (hd : Integrable d) :
    (∫ y, restrictedCorePotential u A y*d y)=
      ∑ s : Spins k, ∑ i : Fin k, ∫ x,
        if position x i ∈ A then (∫ y, coulombKernel (position x i-y)*d y)*‖u.value s x‖^2 else 0 := by
  have H (s : Spins k) (i : Fin k) := restrictedCore_density_prod_integrable u hA s i d hd
  have hi (s : Spins k) (i : Fin k) :
      Integrable (fun y => (∫ x, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2 else 0)*d y) := by
    apply (H s i).integral_prod_right.congr
    filter_upwards [] with y
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    split_ifs <;> simp
  simp only [restrictedCorePotential,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s i))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_finsetSum _ (fun i _ => hi s i)]
  apply Finset.sum_congr rfl
  intro i hi'
  calc
    _ = ∫ y, ∫ x, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2*d y else 0 := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      split_ifs <;> simp
    _ = ∫ x, ∫ y, if position x i ∈ A then coulombKernel (position x i-y)*‖u.value s x‖^2*d y else 0 :=
      (integral_integral_swap (H s i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases h : position x i ∈ A
      · simp only [ite_eq_left h,← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      · simp [h]

lemma restrictedCorePotential_ballCloud {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hA : MeasurableSet A) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hsep : ∀ z ∈ A, a ≤ ‖z-y‖) :
    (∫ z, restrictedCorePotential u A z*ballCloud y a M z)=M*restrictedCorePotential u A y := by
  rw [restrictedCorePotential_fubini u hA _ (ballCloud_integrable a M y)]
  simp only [restrictedCorePotential,Finset.mul_sum,← integral_const_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases h : position x i ∈ A
  · rw [ite_eq_left h,ite_eq_left h,ballCloud_coulomb ha hM y (position x i) (hsep _ h)]
    ring
  · simp [h]

def restrictedOutPotential {m : ℕ} (x : Configuration m) (A : Set Space) (y : Space) : ℝ :=
  ∑ i : Fin m, if position x i ∈ A then coulombKernel (position x i-y) else 0

lemma restrictedOutPotential_nonneg {m : ℕ} (x : Configuration m) (A : Set Space) (y : Space) :
    0 ≤ restrictedOutPotential x A y := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

lemma restrictedOutPotential_mono {m : ℕ} (x : Configuration m) {A B : Set Space}
    (hAB : A ⊆ B) (y : Space) : restrictedOutPotential x A y ≤ restrictedOutPotential x B y := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : position x i ∈ A
  · simp [h,hAB h]
  · simp only [ite_eq_right h]
    split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl

def recordedFarField {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (A : Set Space) (y : Space) : ℝ :=
  attraction S y-restrictedCorePotential u A y-restrictedOutPotential x A y

lemma recordedFarField_le_attraction {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (A : Set Space) (y : Space) : recordedFarField S u x A y ≤ attraction S y := by
  unfold recordedFarField
  linarith [restrictedCorePotential_nonneg u A y,restrictedOutPotential_nonneg x A y]

lemma recordedFarField_anti {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (y : Space) : recordedFarField S u x B y ≤ recordedFarField S u x A y := by
  unfold recordedFarField
  linarith [restrictedCorePotential_mono u hA hB hAB y,restrictedOutPotential_mono x hAB y]

lemma coreField_le_far_addback {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {A : Set Space} (hA : MeasurableSet A) (y : Space) :
    coreScreenedField S u y ≤ recordedFarField S u x A y+restrictedOutPotential x A y := by
  unfold coreScreenedField recordedFarField
  linarith [restrictedCorePotential_le u hA y]

end Coulomb
end

end
end

end OAI
