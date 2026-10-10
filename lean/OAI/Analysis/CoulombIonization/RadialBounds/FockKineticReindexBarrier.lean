import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CutCoreNumber
import OAI.Analysis.CoulombIonization.FormDomain.BlockEnergetics

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

lemma sum_out_reindex {L : ℕ} (b : Fin L → Fin 2) (f : Fin L → ℝ) :
    (∑ i : Fin (cutOutNumber b), f (cutOrder b (finSumFinEquiv (Sum.inr i)))) =
      ∑ i : Fin L, if b i = 1 then f i else 0 := by
  classical
  have hl (i : Fin (cutCoreNumber b)) : b (cutOrder b (finSumFinEquiv (Sum.inl i))) = 0 := by
    have h := congrFun (cutOrder_labels b) (finSumFinEquiv (Sum.inl i))
    simpa only [Function.comp_apply,coreCutLabels,joinLists_left] using h
  have hr (i : Fin (cutOutNumber b)) : b (cutOrder b (finSumFinEquiv (Sum.inr i))) = 1 := by
    have h := congrFun (cutOrder_labels b) (finSumFinEquiv (Sum.inr i))
    simpa only [Function.comp_apply,coreCutLabels,joinLists_right] using h
  rw [← Equiv.sum_comp (cutOrder b),← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [hl,hr,zero_ne_one,ite_false,ite_true,Finset.sum_const_zero,zero_add]

lemma outKinetic_reindex {L : ℕ} (b : Fin L → Fin 2) (ψ : FormVector L) :
    outKinetic (reindexForm (cutOrder b) ψ) =
      (1/2:ℝ)*∑ s : Spins L, ∑ i : Fin L, if b i = 1 then
        (∑ a : Fin 3, ∫ x : Configuration L, ‖ψ.gradient s i a x‖^2) else 0 := by
  classical
  unfold outKinetic
  have he (s : Spins (cutCoreNumber b+cutOutNumber b))
      (i : Fin (cutOutNumber b)) (a : Fin 3) :
      (∫ z, ‖(reindexForm (cutOrder b) ψ).gradient s (finSumFinEquiv (Sum.inr i)) a z‖^2) =
        ∫ x, ‖ψ.gradient (s ∘ (cutOrder b).symm) (cutOrder b (finSumFinEquiv (Sum.inr i))) a x‖^2 :=
    integral_reindex (cutOrder b) (fun x =>
      ‖ψ.gradient (s ∘ (cutOrder b).symm) (cutOrder b (finSumFinEquiv (Sum.inr i))) a x‖^2)
  simp_rw [he]
  have hs (s : Spins (cutCoreNumber b+cutOutNumber b)) :=
    sum_out_reindex b (fun j => ∑ a : Fin 3, ∫ x : Configuration L,
      ‖ψ.gradient (s ∘ (cutOrder b).symm) j a x‖^2)
  simp_rw [hs]
  congr 1
  exact sum_spin_reindex (cutOrder b) (fun s => ∑ i : Fin L, if b i = 1 then
    (∑ a : Fin 3, ∫ x : Configuration L, ‖ψ.gradient s i a x‖^2) else 0)

 def unorderedOutKinetic {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) : ℝ :=
  (1/2:ℝ)*∑ b : Fin L → Fin 2, ∑ s : Spins L, ∑ i : Fin L,
    if b i = 1 then (∑ a : Fin 3, ∫ x,
      ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2) else 0

lemma full_out_kinetic_eq {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) :
    (∑ b : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ b)) =
      unorderedOutKinetic p hp ψ := by
  simp only [orderedCutForm,outKinetic_reindex,unorderedOutKinetic,Finset.mul_sum]

open MeasureTheory Filter
open scoped BigOperators

lemma core_branch_gradient_zero {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (b : Fin L → Fin 2) (s : Spins L) (i : Fin L) (a : Fin 3) (x : Configuration L)
    (hi : b i = 0) (h0 : (p 0).value (x i) = 0)
    (hd : lineDeriv ℝ (p 0).value (x i) (spaceDirections a) = 0) :
    (multiplyForm (spatialProduct p hp b) ψ).gradient s i a x = 0 := by
  classical
  have hv : (spatialProduct p hp b).value x = 0 := by
    change (∏ j, (p (b j)).value (x j)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,h0])
  have hder : lineDeriv ℝ (spatialProduct p hp b).value x (direction i a) = 0 := by
    change lineDeriv ℝ (spatialProductValue p b) x (direction i a) = 0
    rw [spatialProduct_derivative,hi,hd,mul_zero]
  change (↑((spatialProduct p hp b).value x):ℂ)*_+Complex.ofReal
    (lineDeriv ℝ (spatialProduct p hp b).value x (direction i a))*_ = 0
  rw [hv,hder,Complex.ofReal_zero,zero_mul,zero_mul,zero_add]

lemma weighted_gradient_le_out_branches {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (s : Spins L) (i : Fin L) (a : Fin 3) (x : Configuration L) :
    q.value (x i)^2*‖ψ.gradient s i a x‖^2 ≤
      ∑ b : Fin L → Fin 2, if b i = 1 then
        ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0 := by
  classical
  by_cases hq0 : q.value (x i) = 0
  · rw [hq0,zero_pow (by decide : 2 ≠ 0),zero_mul]
    exact Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
  have hfull := finite_partition_gradient (spatialProduct p hp) (spatial_square_partition p hp) ψ s i a x
  have hsum : (∑ b : Fin L → Fin 2, if b i = 1 then
        ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0) =
      ∑ b : Fin L → Fin 2, ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 := by
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with hb
    · rfl
    · have hb0 : b i = 0 := by omega
      rw [core_branch_gradient_zero p hp ψ b s i a x hb0 (hcore _ hq0) (hder _ hq0 a)]
      simp
  rw [hsum,hfull]
  have hq1 : q.value (x i)^2 ≤ 1 := by nlinarith [hq (x i),sq_abs (q.value (x i)),abs_nonneg (q.value (x i))]
  have hh := mul_le_mul_of_nonneg_right hq1 (sq_nonneg ‖ψ.gradient s i a x‖)
  have he : 0 ≤ (∑ j, lineDeriv ℝ (spatialProduct p hp j).value x (direction i a)^2)*‖ψ.value s x‖^2 := by positivity
  nlinarith only [hh,he]

 def localGradientTrace {L : ℕ} (ψ : FormVector L) (q : SmoothMultiplier spaceDirections) : ℝ :=
   ∑ s : Spins L, ∑ i : Fin L, ∑ a : Fin 3,
     ∫ x : Configuration L, q.value (x i)^2*‖ψ.gradient s i a x‖^2

lemma local_gradient_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (q : SmoothMultiplier spaceDirections) (s : Spins L) (i : Fin L) (a : Fin 3) :
    Integrable (fun x : Configuration L => q.value (x i)^2*‖ψ.gradient s i a x‖^2) := by
  have hc : Continuous (fun x : Configuration L => q.value (x i)) :=
    q.regular.continuous.comp (continuous_apply i)
  have hb : ∃ C, ∀ x : Configuration L, |q.value (x i)| ≤ C := by
    obtain ⟨C,hC⟩ := q.bound
    exact ⟨C,fun x => hC (x i)⟩
  have hh := (memLp_bounded_mul hc hb (hψ.2.1 s i a)).norm.integrable_sq
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,Function.comp_apply] using hh

lemma local_gradient_integral_le {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (s : Spins L) (i : Fin L) (a : Fin 3) :
    (∫ x, q.value (x i)^2*‖ψ.gradient s i a x‖^2) ≤
      ∑ b : Fin L → Fin 2, if b i = 1 then
        (∫ x, ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2) else 0 := by
  classical
  have hb (b : Fin L → Fin 2) : Integrable (fun x => if b i = 1 then
      ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2 else 0) := by
    split_ifs
    · exact ((hψ.multiply _).2.1 s i a).norm.integrable_sq
    · exact (integrable_zero _ _ _ : Integrable (fun _ : Configuration L => (0:ℝ)))
  have hh := integral_mono (local_gradient_integrable hψ q s i a)
    (integrable_finsetSum _ (fun b _ => hb b))
    (weighted_gradient_le_out_branches p hp ψ q hq hcore hder s i a)
  rw [integral_finsetSum _ (fun b _ => hb b)] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

 theorem localGradientTrace_le_full_out {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (q : SmoothMultiplier spaceDirections) (hq : ∀ x, |q.value x| ≤ 1)
    (hcore : ∀ x, q.value x ≠ 0 → (p 0).value x = 0)
    (hder : ∀ x, q.value x ≠ 0 → ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0) :
    localGradientTrace ψ q ≤ 2*∑ b : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ b) := by
  classical
  rw [full_out_kinetic_eq,unorderedOutKinetic]
  rw [←mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Spins L))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) =>
      Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
        local_gradient_integral_le hψ p hp q hq hcore hder s i a)))
  apply hh.trans_eq
  conv_lhs => arg 2; ext s; arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  split_ifs <;> simp

end CoulombAtom

end

end OAI
