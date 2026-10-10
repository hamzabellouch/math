import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedInnerCap
import OAI.Analysis.CoulombIonization.Variational.ClosedInnerStatistic

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom
attribute [local irreducible] oneBodySquareTotal graphFormVector fermionGraph

def closedShellField {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) : ℝ := ∑ i, p.value (x i)^2*closedRawInnerField Z h x (x i)
def shellMeanField {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) : ℝ := closedShellField p Z h x/(oneBodySquareTotal p).value x

lemma oneBodySquareTotal_nonneg {N : ℕ} (p : SmoothMultiplier spaceDirections) (x : Configuration N) :
    0 ≤ (oneBodySquareTotal p).value x := by
  rw [oneBodySquareTotal_value]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
lemma closedShellField_measurable (N : ℕ) (p : SmoothMultiplier spaceDirections) (Z h : ℝ) :
    Measurable (closedShellField (N := N) p Z h) := by
  unfold closedShellField
  apply Finset.measurable_sum
  intro i _
  have h1 : Measurable (fun x : Configuration N => p.value (x i)) :=
    p.regular.continuous.measurable.comp (measurable_pi_apply i)
  have h2 : Measurable (fun x : Configuration N => (x,x i)) :=
    measurable_id.prodMk (measurable_pi_apply i)
  have h3 : Measurable (fun x : Configuration N => closedRawInnerField Z h x (x i)) :=
    by simpa only [Function.comp_def] using (closedRawInnerField_measurable N Z h).comp h2
  exact (h1.pow_const 2).mul h3

lemma shellMeanField_measurable (N : ℕ) (p : SmoothMultiplier spaceDirections) (Z h : ℝ) :
    Measurable (shellMeanField (N := N) p Z h) :=
  (closedShellField_measurable N p Z h).div (oneBodySquareTotal p).regular.continuous.measurable

lemma closedShellField_bound {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (x : Configuration N) :
    |closedShellField p Z h x| ≤ (|Z|/(2*a)+(N:ℝ)/a)*(oneBodySquareTotal p).value x := by
  calc
    _ ≤ ∑ i, |p.value (x i)^2*closedRawInnerField Z h x (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Z|/(2*a)+(N:ℝ)/a)*p.value (x i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p.value (x i) = 0
      · simp only [hi,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,abs_zero,le_refl]
      · rw [abs_mul,abs_of_nonneg (sq_nonneg _),mul_comm (p.value (x i)^2)]
        exact mul_le_mul_of_nonneg_right (closedRawInnerField_bound Z ha (by linarith) (hp _ hi) x) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,oneBodySquareTotal_value]

lemma shellMeanField_bound {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (x : Configuration N) :
    ‖shellMeanField p Z h x‖ ≤ |Z|/(2*a)+(N:ℝ)/a := by
  unfold shellMeanField
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (oneBodySquareTotal_nonneg p x)]
  by_cases hs : (oneBodySquareTotal p).value x = 0
  · rw [hs,div_zero]; positivity
  · apply (div_le_iff₀ ((oneBodySquareTotal_nonneg p x).lt_of_ne' hs)).2
    exact closedShellField_bound p Z ha hh hp x

lemma oneBodySquareTotal_reindex {M N : ℕ} (p : SmoothMultiplier spaceDirections)
    (e : Fin M ≃ Fin N) (x : Configuration M) :
    (oneBodySquareTotal p).value (x ∘ e.symm) = (oneBodySquareTotal p).value x :=
  by simpa only [oneBodySquareTotal_value,Function.comp_apply] using Equiv.sum_comp e.symm (fun i => p.value (x i)^2)
lemma closedShellField_reindex {M N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (e : Fin M ≃ Fin N) (x : Configuration M) :
    closedShellField p Z h (x ∘ e.symm) = closedShellField p Z h x := by
  unfold closedShellField
  simp_rw [closedRawInnerField_reindex]
  exact Equiv.sum_comp e.symm (fun i => p.value (x i)^2*closedRawInnerField Z h x (x i))

def shellMeanStatistic (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) : FullStatistic where
  value := fun _ => shellMeanField p Z h
  measurable := fun N => shellMeanField_measurable N p Z h
  bounded := fun N => ⟨|Z|/(2*a)+(N:ℝ)/a,shellMeanField_bound p Z ha hh hp⟩
  reindex := fun e x => by unfold shellMeanField; rw [closedShellField_reindex,oneBodySquareTotal_reindex]

lemma oneBodySquareTotal_join {N M : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) (v : Configuration M) :
    (oneBodySquareTotal p).value (joinLists x v) =
      (oneBodySquareTotal p).value x+(oneBodySquareTotal p).value v := by
  simpa only [oneBodySquareTotal_value,rawWeightedCount] using rawWeightedCount_join (fun z => p.value z^2) x v

lemma closedShellField_join {N M : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) (v : Configuration M) (hx : ∀ i, p.value (x i) = 0)
    (hv : ∀ i, h < ‖v i‖) :
    closedShellField p Z h (joinLists x v) =
      ∑ i, p.value (v i)^2*closedRawInnerField Z h x (v i) := by
  unfold closedShellField
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [joinLists_left,joinLists_right,closedRawInnerField_join Z h x v hv,hx,
    zero_pow (by decide : 2 ≠ 0),zero_mul,Finset.sum_const_zero,zero_add]

lemma shellMeanField_join {N M : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) (v : Configuration M) (hx : ∀ i, p.value (x i) = 0)
    (hv : ∀ i, h < ‖v i‖) :
    shellMeanField p Z h (joinLists x v) =
      (∑ i, p.value (v i)^2*closedRawInnerField Z h x (v i))/(oneBodySquareTotal p).value v := by
  unfold shellMeanField
  rw [closedShellField_join p Z h x v hx hv,oneBodySquareTotal_join]
  have hz : (oneBodySquareTotal p).value x = 0 := by
    simp only [oneBodySquareTotal_value,hx,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  rw [hz,zero_add]

lemma oneBodySquareTotal_mul_shellMeanField {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (x : Configuration N) :
    (oneBodySquareTotal p).value x*shellMeanField p Z h x = closedShellField p Z h x := by
  unfold shellMeanField
  by_cases hs : (oneBodySquareTotal p).value x = 0
  · have hi : ∀ i, p.value (x i) = 0 := by
      intro i
      have hh := Finset.single_le_sum (f := fun j : Fin N => p.value (x j)^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [←oneBodySquareTotal_value] at hh
      rw [hs] at hh
      nlinarith only [hh,sq_nonneg (p.value (x i))]
    simp only [hs,zero_mul,closedShellField,hi,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  · exact mul_div_cancel₀ _ hs
end CoulombAtom

end

end OAI
