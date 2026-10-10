import Mathlib
import OAI.Analysis.CoulombRadii.Localization.CutCombinatorics
import OAI.Analysis.CoulombRadii.RandomFields.CutJensen

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma tensorCut_selected_square {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (hp : ∀ y, ∑ l, χ l y^2=1) (i : Fin n) (x : Configuration n) :
    (∑ p : Fin n → Fin 2, if p i=0 then (tensorCut χ p x)^2 else 0)=χ 0 (position x i)^2 := by
  have he (p : Fin n → Fin 2) :
      (if p i=0 then (tensorCut χ p x)^2 else 0)=
        (if p i=0 then χ 0 (position x i)^2 else 0)*
          ∏ j∈Finset.univ.erase i, χ (p j) (position x j)^2 := by
    unfold tensorCut
    rw [←Finset.prod_pow,←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  simp_rw [he]
  rw [sum_slot_product (fun j l => χ l (position x j)^2)
    (fun l => if l=0 then χ 0 (position x i)^2 else 0) i (fun j => hp _)]
  simp

def coloredObservable {n : ℕ} (F : Fin n → Configuration n → ℝ)
    (p : Fin n → Fin 2) (x : Configuration n) : ℝ :=
  ∑ i, if p i=0 then F i x else 0

lemma coloredObservable_measurable {n : ℕ} {F : Fin n → Configuration n → ℝ}
    (hF : ∀ i, Measurable (F i)) (p : Fin n → Fin 2) : Measurable (coloredObservable F p) := by
  apply Finset.measurable_fun_sum
  intro i hi
  by_cases h : p i=0 <;> simp only [h,ite_true,ite_false]
  · exact hF i
  · exact measurable_const

lemma coloredObservable_abs_le {n : ℕ} {F : Fin n → Configuration n → ℝ} {B : ℝ}
    (hB : 0≤B) (hb : ∀ i x, |F i x|≤B) (p : Fin n → Fin 2) (x : Configuration n) :
    |coloredObservable F p x|≤(n:ℝ)*B := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have H : (∑ i : Fin n, |if p i=0 then F i x else 0|) ≤ ∑ _i : Fin n, B := by
    apply Finset.sum_le_sum
    intro i hi
    split_ifs
    · exact hb i x
    · exact (abs_zero).le.trans hB
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma tensorCut_colored_sum {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (hp : ∀ y, ∑ l, χ l y^2=1) (F : Fin n → Configuration n → ℝ) (x : Configuration n) :
    (∑ p : Fin n → Fin 2, coloredObservable F p x*(tensorCut χ p x)^2)=
      ∑ i, χ 0 (position x i)^2*F i x := by
  simp only [coloredObservable,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he (p : Fin n → Fin 2) : (if p i=0 then F i x else 0)*(tensorCut χ p x)^2=
      (if p i=0 then (tensorCut χ p x)^2 else 0)*F i x := by
    split_ifs <;> ring
  simp_rw [he]
  rw [←Finset.sum_mul,tensorCut_selected_square χ hp]

lemma potentialForm_colored_labelCut {n : ℕ} (u : H1Vector n)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    (F : Fin n → Configuration n → ℝ) (hF : ∀ i, Measurable (F i))
    {B : ℝ} (hB : 0≤B) (hb : ∀ i x, |F i x|≤B) :
    (∑ p : Fin n → Fin 2, potentialForm (coloredObservable F p) (u.labelCut χ hχ hp D hD hd p))=
      potentialForm (fun x => ∑ i, χ 0 (position x i)^2*F i x) u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => boundedObservable_integrable
    (u.labelCut χ hχ hp D hD hd p) (coloredObservable F p)
    (coloredObservable_measurable hF p) (coloredObservable_abs_le hB hb p) s)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (∑ p, coloredObservable F p x*‖(tensorCut χ p x : ℂ)*u.value s x‖^2)=_
  simp only [norm_real_mul_sq,←mul_assoc,←Finset.sum_mul,tensorCut_colored_sum χ hp]

end Coulomb
end

end

end OAI
