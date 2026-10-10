import Mathlib
import OAI.Probability.ThreeStateClauses.RegularCritical

namespace OAI

/-! Regular Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma finite_abs_bound (f : α → ℝ) : ∃ C : ℝ, ∀ a, |f a| ≤ C := by
  obtain ⟨C,hC⟩ := (Set.finite_range (fun a ↦ |f a|)).bddAbove
  exact ⟨C, fun a ↦ hC ⟨a,rfl⟩⟩

lemma integral_pmf_bind_finite (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  obtain ⟨C,hC⟩ := finite_abs_bound f
  exact integral_pmf_bind p K hC

lemma integral_product_sum (p : PMF α) (f : α → ℝ) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j)) ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a ∂p.toMeasure) := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) Integrable.of_finite (by simp)

lemma integral_product_sq_sum (p : PMF α) (f : α → ℝ) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j))^2 ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a^2 ∂p.toMeasure)+((n:ℝ)^2-n)*(∫ a, f a ∂p.toMeasure)^2 := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) Integrable.of_finite Integrable.of_finite (by simp)

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def spinScore (i : Spin) : ℝ := if i=0 then 2 else -1

lemma spinScore_abs (i : Spin) : |spinScore i| ≤ 2 := by
  unfold spinScore; split_ifs <;> norm_num

lemma spinScore_square (i : Spin) : spinScore i^2 ≤ 4 := by
  unfold spinScore; split_ifs <;> norm_num

lemma channel_spinScore (lam : ℝ) (hlam : Admissible lam) (i : Spin) :
    (∫ j, spinScore j ∂(channel lam hlam i).toMeasure) = lam*spinScore i := by
  rw [PMF.integral_eq_sum]
  have he (j : Spin) : (channel lam hlam i j).toReal = channelWeight lam i j :=
    ENNReal.toReal_ofReal (channelWeight_nonneg hlam i j)
  simp only [smul_eq_mul, he]
  simp_rw [channelWeight_alt, add_mul, Finset.sum_add_distrib]
  have hs : ∑ j : Spin, spinScore j = 0 := by
    norm_num [Fin.sum_univ_three, spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.mul_sum, hs, mul_zero, add_zero]

def regularStatistic (b : ℕ) (lam : ℝ) : (ℓ : ℕ) → RegularObservation b ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, v => (∑ j : Fin b, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam)

def observedRegularStatistic (b : ℕ) (lam : ℝ) : (ℓ : ℕ) → Observation ℓ → ℝ
  | 0, i => spinScore i
  | ℓ+1, s => if s.card = b then (s.map (observedRegularStatistic b lam ℓ)).sum/((b:ℝ)*lam) else 0

lemma abs_multiset_sum_bound {α : Type*} (f : α → ℝ) (C : ℝ) (hf : ∀ a, |f a| ≤ C)
    (s : Multiset α) : |(s.map f).sum| ≤ (s.card:ℝ)*C := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (by linarith [hf a])

lemma observedRegularStatistic_bound (b : ℕ) (lam : ℝ) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ o, |observedRegularStatistic b lam ℓ o| ≤ C := by
  induction ℓ with
  | zero => exact ⟨2, by norm_num, spinScore_abs⟩
  | succ ℓ ih =>
    obtain ⟨C,hC,hbound⟩ := ih
    refine ⟨(b:ℝ)*C/|((b:ℝ)*lam)|, by positivity, ?_⟩
    intro s
    change |if s.card=b then _ else 0| ≤ _
    split_ifs with h
    · rw [abs_div]
      exact div_le_div_of_nonneg_right (by simpa only [h] using abs_multiset_sum_bound _ C hbound s) (abs_nonneg _)
    · simp only [abs_zero]; positivity

lemma observedRegularStatistic_forget (b : ℕ) (lam : ℝ) (ℓ : ℕ)
    (v : RegularObservation b ℓ) :
    observedRegularStatistic b lam ℓ (forgetRegular b ℓ v) = regularStatistic b lam ℓ v := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    simp only [forgetRegular, observedRegularStatistic, Multiset.coe_card, List.length_ofFn, ite_true, regularStatistic]
    congr 1
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Function.comp_def, ih, List.sum_ofFn]

lemma regularStatistic_mean (b : ℕ) (hb : 0 < b) (lam : ℝ) (hlam : Admissible lam)
    (hl : lam ≠ 0) (ℓ : ℕ) (i : Spin) :
    (∫ v, regularStatistic b lam ℓ v ∂(regularLaw b lam hlam ℓ i).toMeasure) = spinScore i := by
  have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v ∂(PMF.pure i).toMeasure) = spinScore i
    rw [PMF.toMeasure_pure, integral_dirac]
  | succ ℓ ih =>
    change (∫ v, (∑ j : Fin b, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam)
      ∂(productPMF (fun _ ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).toMeasure) = _
    rw [integral_div, integral_product_sum, integral_pmf_bind_finite]
    simp_rw [ih]
    rw [channel_spinScore]
    field_simp

end ThreeState.TreeClauses.Tree

end

end OAI
