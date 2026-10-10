import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalPositiveField

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma boundedObservable_integrable {n : ℕ} (u : H1Vector n) (W : Configuration n → ℝ)
    (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) (s : Spins n) :
    Integrable (fun x => W x*‖u.value s x‖^2) := by
  exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).bdd_mul hW.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

lemma potentialForm_abs_le {n : ℕ} (u : H1Vector n) (W : Configuration n → ℝ)
    (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    |potentialForm W u| ≤ B*mass u := by
  rw [abs_le]
  have h (s : Spins n) : -(B*(∫ x, ‖u.value s x‖^2)) ≤ ∫ x, W x*‖u.value s x‖^2 ∧
      (∫ x, W x*‖u.value s x‖^2) ≤ B*(∫ x, ‖u.value s x‖^2) := by
    constructor
    · rw [← integral_const_mul,← integral_neg]
      apply integral_mono (((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B).neg
        (boundedObservable_integrable u W hW hB s)
      intro x
      have H := (abs_le.mp (hB x)).1
      dsimp only [Pi.neg_apply]
      nlinarith [sq_nonneg ‖u.value s x‖,mul_le_mul_of_nonneg_right H (sq_nonneg ‖u.value s x‖)]
    · rw [← integral_const_mul]
      exact integral_mono (boundedObservable_integrable u W hW hB s)
        (((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B)
        (fun x => mul_le_mul_of_nonneg_right (abs_le.mp (hB x)).2 (sq_nonneg _))
  constructor
  · simpa only [potentialForm,mass,Finset.sum_neg_distrib,←Finset.mul_sum] using
      Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => (h s).1)
  · simpa only [potentialForm,mass,←Finset.mul_sum] using
      Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => (h s).2)

lemma mass_normalized_le_one {n : ℕ} (u : H1Vector n) : mass u.normalized ≤ 1 := by
  by_cases h : mass u=0
  · simp [H1Vector.normalized,mass_rsmul,h]
  · exact (mass_normalized u (lt_of_le_of_ne (mass_nonneg u) (Ne.symm h))).le

def coreConditionalObservable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (s : Spins m) (x : Configuration m) : ℝ :=
  potentialForm (fun v => W (joinConfiguration m k (x,v))) (u.coreSlice s x).normalized

lemma coreConditionalObservable_abs_le {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) (x : Configuration m) :
    |coreConditionalObservable u W s x| ≤ B := by
  apply (potentialForm_abs_le _ _ (hW.comp ((joinConfiguration m k).continuous.measurable.comp
    (measurable_const.prodMk measurable_id))) (fun v => hB _)).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (mass_normalized_le_one (u.coreSlice s x)) hB0

lemma coreConditionalObservable_aestronglyMeasurable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B)
    (s : Spins m) : AEStronglyMeasurable (coreConditionalObservable u W s) volume := by
  unfold coreConditionalObservable
  simp only [potentialForm_normalized_eq]
  apply (mass_coreSlice_integrable u s).aestronglyMeasurable.inv₀.mul
  apply (potentialForm_coreSlice_parameter_integrable u s (fun x v => W (joinConfiguration m k (x,v))) ?_).aestronglyMeasurable
  intro t
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using
    boundedObservable_integrable u W hW hB (Fin.append s t)

lemma coreConditionalObservable_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*coreConditionalObservable u W s x) := by
  exact (mass_coreSlice_integrable u s).mul_bdd
    (coreConditionalObservable_aestronglyMeasurable u W hW hB s)
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using
      (coreConditionalObservable_abs_le u W hW hB0 hB s x)))

lemma coreConditionalObservable_positive_weight_integrable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |W x| ≤ B) (s : Spins m) (q : ℕ) :
    Integrable (fun x => mass (u.coreSlice s x)*(max (coreConditionalObservable u W s x) 0)^q) := by
  apply (mass_coreSlice_integrable u s).mul_bdd
    (((coreConditionalObservable_aestronglyMeasurable u W hW hB s).sup aestronglyMeasurable_const).pow q)
  filter_upwards [] with x
  change ‖(max (coreConditionalObservable u W s x) 0)^q‖ ≤ B^q
  rw [Real.norm_of_nonneg (pow_nonneg (le_max_right _ _) q)]
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le (le_trans (le_abs_self _)
    (coreConditionalObservable_abs_le u W hW hB0 hB s x)) hB0) q

lemma sliceExpectation_coreConditionalObservable {m k : ℕ} (u : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x| ≤ B) :
    sliceExpectation u (coreConditionalObservable u W)=potentialForm W u := by
  unfold sliceExpectation coreConditionalObservable
  simp_rw [potentialForm_normalized_weight]
  have H := integral_potentialForm_coreSlice_parameter u (fun x v => W (joinConfiguration m k (x,v)))
    (fun st => by simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using
      boundedObservable_integrable u W hW hB st)
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,potentialForm] using H

theorem conditional_ensemble_positive_jensen {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (W : (p : P) → Configuration (m p+k p) → ℝ)
    (hW : ∀ p, Measurable (W p)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ p x, |W p x| ≤ B) (hmass : (∑ p, mass (u p))=1) :
    (max (∑ p, potentialForm (W p) (u p)) 0)^2 ≤
      ∑ p, sliceExpectation (u p) (fun s x => (max (coreConditionalObservable (u p) (W p) s x) 0)^2) := by
  let F := fun p => coreConditionalObservable (u p) (W p)
  let c : ℝ := ∑ p, sliceExpectation (u p) (fun s x => max (F p s x) 0)
  have hp (p) (s : Spins (m p)) : Integrable (fun x => mass ((u p).coreSlice s x)*max (F p s x) 0) := by
    simpa only [pow_one] using coreConditionalObservable_positive_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s 1
  have hq (p) (s : Spins (m p)) := coreConditionalObservable_positive_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s 2
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ =>
    integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (le_max_right _ _))))
  have hc : max (∑ p, potentialForm (W p) (u p)) 0 ≤ c := by
    apply max_le _ hc0
    apply Finset.sum_le_sum
    intro p _
    rw [←sliceExpectation_coreConditionalObservable (u p) (W p) (hW p) (hB p)]
    apply Finset.sum_le_sum
    intro s _
    exact integral_mono (coreConditionalObservable_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s)
      (hp p s) (fun x => mul_le_mul_of_nonneg_left (le_max_left _ _) (mass_nonneg _))
  have hn : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0-c)^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have he (p) (s : Spins (m p)) :
      (∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0-c)^2) =
      (∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0)^2)-
      2*c*(∫ x, mass ((u p).coreSlice s x)*max (F p s x) 0)+
      c^2*(∫ x, mass ((u p).coreSlice s x)) := by
    have hi : Integrable (fun x => mass ((u p).coreSlice s x)*(max (F p s x) 0)^2-
        (2*c)*(mass ((u p).coreSlice s x)*max (F p s x) 0)) := by
      exact (hq p s).sub ((hp p s).const_mul (2*c))
    calc
      _ = ∫ x, (mass ((u p).coreSlice s x)*(max (F p s x) 0)^2-
          (2*c)*(mass ((u p).coreSlice s x)*max (F p s x) 0))+c^2*mass ((u p).coreSlice s x) :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by rw [integral_add hi ((mass_coreSlice_integrable (u p) s).const_mul _),
        integral_sub (hq p s) ((hp p s).const_mul _),integral_const_mul,integral_const_mul]
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,integral_mass_coreSlice,hmass,mul_one] at hn
  change 0 ≤ (∑ p, sliceExpectation (u p) (fun s x => (max (F p s x) 0)^2))-2*c*c+c^2 at hn
  have H := pow_le_pow_left₀ (le_max_right (∑ p, potentialForm (W p) (u p)) 0) hc 2
  dsimp [F] at hn
  nlinarith

end Coulomb
end

end
end

end OAI
