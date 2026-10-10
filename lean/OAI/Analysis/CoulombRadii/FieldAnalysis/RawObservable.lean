import Mathlib
import OAI.Analysis.CoulombRadii.Localization.CutCombinatorics
import OAI.Analysis.CoulombRadii.RandomFields.CutJensen
import OAI.Analysis.CoulombRadii.FieldAnalysis.FarSubmean

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def rawSignedField {n : ℕ} (V : ℝ) (A : Set Space) (y : Space) (x : Configuration n) : ℝ :=
  V-restrictedOutPotential x A y

lemma restrictedOutPotential_measurable_configuration {n : ℕ} {A : Set Space}
    (hA : MeasurableSet A) (y : Space) : Measurable (fun x : Configuration n => restrictedOutPotential x A y) := by
  apply Finset.measurable_fun_sum
  intro i hi
  apply Measurable.ite (hA.preimage (continuous_position i).measurable) _ measurable_const
  simp only [coulombKernel]
  have hm : Measurable (fun x : Configuration n => position x i) := (continuous_position i).measurable
  fun_prop

lemma rawSignedField_measurable {n : ℕ} (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) :
    Measurable (rawSignedField (n:=n) V A y) :=
  measurable_const.sub (restrictedOutPotential_measurable_configuration hA y)

lemma rawSignedField_abs_le {n : ℕ} (V : ℝ) (A : Set Space) (y : Space)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (x : Configuration n) :
    |rawSignedField V A y x| ≤ |V|+(n:ℝ)/r := by
  have H := restrictedOutPotential_le x A hr y hsep
  have H0 := restrictedOutPotential_nonneg x A y
  unfold rawSignedField
  calc
    _ ≤ |V|+|restrictedOutPotential x A y| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg H0]; linarith

lemma restrictedOutPotential_permute {n : ℕ} (p : Equiv.Perm (Fin n))
    (x : Configuration n) (A : Set Space) (y : Space) :
    restrictedOutPotential (permute p x) A y=restrictedOutPotential x A y := by
  simp only [restrictedOutPotential,position_permute]
  exact Equiv.sum_comp p (fun i : Fin n => if position x i ∈ A then coulombKernel (position x i-y) else 0)

lemma rawSignedField_permute {n : ℕ} (V : ℝ) (A : Set Space) (y : Space)
    (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    rawSignedField V A y (permute p x)=rawSignedField V A y x := by
  simp only [rawSignedField,restrictedOutPotential_permute]

lemma restrictedOutPotential_join {m k : ℕ} (x : Configuration m) (v : Configuration k)
    (A : Set Space) (y : Space) :
    restrictedOutPotential (joinConfiguration m k (x,v)) A y =
      restrictedOutPotential x A y+restrictedOutPotential v A y := by
  simp only [restrictedOutPotential,Fin.sum_univ_add,position_join_left,position_join_right]

lemma potentialForm_restrictedOutPotential {n : ℕ} (u : H1Vector n) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) :
    potentialForm (fun x => restrictedOutPotential x A y) u=restrictedCorePotential u A y := by
  apply Finset.sum_congr rfl
  intro s hs
  unfold restrictedOutPotential
  simp only [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; split_ifs <;> simp)
  · intro i hi
    exact (restrictedCore_integrable u hA s i y).congr (Eventually.of_forall (fun x => by dsimp only; split_ifs <;> simp))

lemma potentialForm_rawSignedField {n : ℕ} (u : H1Vector n) (V : ℝ) {A : Set Space}
    (hA : MeasurableSet A) (y : Space) {r : ℝ} (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) :
    potentialForm (rawSignedField V A y) u=V*mass u-restrictedCorePotential u A y := by
  rw [←potentialForm_const,←potentialForm_restrictedOutPotential u hA y]
  unfold potentialForm rawSignedField
  simp only [sub_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_sub]
  · exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul V
  · exact boundedObservable_integrable u _ (restrictedOutPotential_measurable_configuration hA y)
      (fun x => by rw [abs_of_nonneg (restrictedOutPotential_nonneg x A y)]; exact restrictedOutPotential_le x A hr y hsep) s

lemma coreConditionalObservable_rawSignedField {m k : ℕ} (u : H1Vector (m+k))
    (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (s : Spins m) (x : Configuration m)
    (hm : 0 < mass (u.coreSlice s x)) :
    coreConditionalObservable u (rawSignedField V A y) s x =
      V-restrictedCorePotential (u.coreSlice s x).normalized A y-restrictedOutPotential x A y := by
  unfold coreConditionalObservable
  have he : (fun v => rawSignedField V A y (joinConfiguration m k (x,v))) =
      rawSignedField (V-restrictedOutPotential x A y) A y := by
    funext v
    simp only [rawSignedField,restrictedOutPotential_join]
    ring
  rw [he,potentialForm_rawSignedField _ _ hA y hr hsep,mass_normalized _ hm,mul_one]
  ring

lemma coreConditionalObservable_raw_positive_weight {m k : ℕ} (u : H1Vector (m+k))
    (V : ℝ) {A : Set Space} (hA : MeasurableSet A) (y : Space) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ v ∈ A, r ≤ ‖v-y‖) (s : Spins m) (x : Configuration m) :
    mass (u.coreSlice s x)*(max (coreConditionalObservable u (rawSignedField V A y) s x) 0)^2 =
      mass (u.coreSlice s x)*(max (V-restrictedCorePotential (u.coreSlice s x).normalized A y-
        restrictedOutPotential x A y) 0)^2 := by
  by_cases h : mass (u.coreSlice s x)=0
  · simp only [h,zero_mul]
  · rw [coreConditionalObservable_rawSignedField u V hA y hr hsep s x
      (lt_of_le_of_ne (mass_nonneg _) (Ne.symm h))]

lemma potentialForm_labelCut {n : ℕ} {L : Type*} [Fintype L] (u : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (W : Configuration n → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    (∑ p : Fin n → L, potentialForm W (u.labelCut χ hχ hp D hD hd p))=potentialForm W u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact potential_smooth_partition u _ (tensorCut_contDiff χ hχ) 1 D (tensorCut_abs_le_one χ hp)
    (tensorCut_partial_bound χ hχ hp hD hd) (tensorCut_partition χ hp) W s
    (fun p => boundedObservable_integrable (u.labelCut χ hχ hp D hD hd p) W hW hB s)

end Coulomb
end

end
end

end OAI
