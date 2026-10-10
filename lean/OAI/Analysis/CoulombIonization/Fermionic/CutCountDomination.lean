import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialPatchGeometry
import OAI.Analysis.CoulombIonization.Localization.FormRawLaw

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom
open CoulombRadialAveraging

def spatialCutExpectation {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector N)
    (F : (Fin N → Fin 2) → Configuration N → ℝ) : ℝ :=
  ∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
    F c x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2

lemma spatialCutExpectation_raw {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    spatialCutExpectation p hp ψ (fun _ => g) = ∫ x, g x ∂formRawLaw ψ := by
  rw [formRawLaw_integral_eq_spin_sum hψ hg hB]
  unfold spatialCutExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (c : Fin N → Fin 2) : Integrable (fun x =>
      g x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) :=
    (((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)
  rw [←integral_finsetSum _ (fun c _ => hi c)]
  apply integral_congr_ae (ae_of_all _ _)
  intro x
  rw [←Finset.mul_sum,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]

lemma spatialCutExpectation_le_raw {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    {F : (Fin N → Fin 2) → Configuration N → ℝ} {g : Configuration N → ℝ}
    (hF : ∀ c, Measurable (F c)) {A : ℝ} (hA : ∀ c x, ‖F c x‖ ≤ A)
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hfg : ∀ c x, (spatialProduct p hp c).value x ≠ 0 → F c x ≤ g x) :
    spatialCutExpectation p hp ψ F ≤ ∫ x, g x ∂formRawLaw ψ := by
  rw [←spatialCutExpectation_raw p hp hψ hg hB]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  apply integral_mono
    ((((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul (hF c).aestronglyMeasurable
      (ae_of_all _ (hA c)))
    ((((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable
      (ae_of_all _ hB))
  intro x
  by_cases hx : (spatialProduct p hp c).value x = 0
  · simp only [multiplyForm,hx,Complex.ofReal_zero,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hfg c x hx) (sq_nonneg _)

lemma spatialCutExpectation_outMoment {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector N)
    (q : ℕ → ℝ) :
    (∑ c : Fin N → Fin 2, q (cutOutNumber c)*formMass (orderedCutForm p hp ψ c)) =
      spatialCutExpectation p hp ψ (fun c _ => q (cutOutNumber c)) := by
  simp_rw [orderedCutForm_mass]
  simp only [spatialCutExpectation,formMass,Finset.mul_sum,integral_const_mul]

lemma radialCut_out_distance {N : ℕ} (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin N) (hi : c i ≠ 0) : ‖x i-y‖ < t+b := by
  classical
  have hc : c i = 1 := by omega
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  have hf : (coreFirstRadialCut y ht hb (c i)).value (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  by_contra hh
  have hz := (radialCut_outer ht hb (le_of_not_gt hh)).1
  apply hf
  simpa only [hc,coreFirstRadialCut,radialCut,Matrix.cons_val_one,Matrix.cons_val_zero] using hz

lemma radialCut_outNumber_le_rawBall {N : ℕ} (y : Space) {t b R : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    (cutOutNumber c:ℝ) ≤ rawBallCount y R x := by
  classical
  rw [cutOutNumber_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : c i ≠ 0
  · have hd := lt_of_lt_of_le (radialCut_out_distance y ht hb c x hx i hi) hR
    simp [hi,hd]
  · simp only [hi,ite_false]
    split_ifs <;> norm_num

def cutDeletedCount {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : ℝ :=
  ∑ i, if c i ≠ 0 ∧ t-7*b ≤ ‖x i-y‖ then 1 else 0

lemma cutDeletedCount_nonneg {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : 0 ≤ cutDeletedCount y t b c x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma cutDeletedCount_le {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : cutDeletedCount y t b c x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma cutDeletedCount_measurable {N : ℕ} (y : Space) (t b : ℝ) (c : Fin N → Fin 2) :
    Measurable (cutDeletedCount y t b c) := by
  apply Finset.measurable_sum; intro i _
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hc : c i ≠ 0
  · simpa [hc] using (measurableSet_le (measurable_const (a := t-7*b))
      (configuration_distance_measurable y i))
  · simp [hc]

lemma radialCut_deleted_le_rawStrip {N : ℕ} (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    cutDeletedCount y t b c x ≤ rawStripCount y t b x := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hh : c i ≠ 0 ∧ t-7*b ≤ ‖x i-y‖
  · have hd := radialCut_out_distance y ht hb c x hx i hh.1
    have hs : ‖x i-y‖-b ≤ t ∧ t ≤ ‖x i-y‖+7*b := ⟨by linarith,by linarith [hh.2]⟩
    simp [hh,slidingBit,hs]
  · simp only [hh,ite_false]
    exact slidingBit_nonneg _ _ _ _

end CoulombAtom

end

end OAI
