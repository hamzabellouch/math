import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.AllEmptyIndicator

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι H : Type*} [Fintype ι]

noncomputable def emptyWeight {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (ω : Fin R→ι→ℕ) : ℝ :=
  ∑h∈E,w h*allEmptyIndicator (lines h) ω

omit [Fintype ι] in
lemma emptyWeight_eq_sum {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (ω : Fin R→ι→ℕ) :
    emptyWeight E lines w ω=∑h∈emptyTests E lines ω,w h := by
  simp only [emptyWeight,allEmptyIndicator_eq_if,emptyTests,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> simp

omit [Fintype ι] in
lemma emptyWeight_nonneg {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (hw : ∀h∈E,0≤w h) (ω : Fin R→ι→ℕ) :
    0≤emptyWeight E lines w ω :=
  Finset.sum_nonneg fun h hh => mul_nonneg (hw h hh) (allEmptyIndicator_bounds _ _).1

lemma integrable_emptyWeight (rate : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) (w : H→ℝ) :
    Integrable (emptyWeight (R:=R) E lines w) (scheduleMeasure rate R) :=
  integrable_finsetSum E fun h _ => (integrable_allEmptyIndicator rate (lines h)).const_mul (w h)

lemma integral_emptyWeight (rate : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) (w : H→ℝ) :
    (∫ ω,emptyWeight E lines w ω ∂scheduleMeasure rate R)=
      ∑h∈E,w h*Real.exp (-(R:ℝ)*mass rate (lines h)) := by
  unfold emptyWeight
  rw [integral_finsetSum E (fun h _ => (integrable_allEmptyIndicator rate (lines h)).const_mul (w h))]
  simp only [integral_const_mul,integral_allEmptyIndicator]

omit [Fintype ι] in
lemma emptyWeight_light_heavy {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) {a : ℝ} (ha : 0≤a) (ω : Fin R→ι→ℕ) :
    emptyWeight E lines w ω ≤ a*((emptyTests E lines ω).card:ℝ)+
      emptyWeight (E.filter fun h => a<w h) lines w ω := by
  rw [emptyTests_card,Finset.mul_sum]
  unfold emptyWeight
  rw [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hs : a<w h
  · simp only [hs,ite_true]
    exact le_add_of_nonneg_left (mul_nonneg ha (allEmptyIndicator_bounds _ _).1)
  · simp only [hs,ite_false,add_zero]
    exact mul_le_mul_of_nonneg_right (le_of_not_gt hs) (allEmptyIndicator_bounds _ _).1

lemma heavy_empty_mean (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) {a M : ℝ}
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    (∫ ω,emptyWeight (E.filter fun h => a < mass weight (lines h)) lines
      (fun h => mass weight (lines h)) ω ∂scheduleMeasure (fun i => L*weight i) R) ≤
        M*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
  rw [integral_emptyWeight]
  have hmass : ∀h,0≤ mass weight (lines h) := fun h =>
    Finset.sum_nonneg fun i _ => (weight i).coe_nonneg
  calc
    _ ≤ ∑h∈E.filter (fun h => a < mass weight (lines h)),
        mass weight (lines h)*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (hmass h)
      apply Real.exp_le_exp.mpr
      have hscaled : mass (fun i => L*weight i) (lines h)=(L:ℝ)*mass weight (lines h) := by
        simp only [mass,NNReal.coe_mul,Finset.mul_sum]
      rw [hscaled]
      have hm := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hh).2.le
        (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg R) L.coe_nonneg))
      nlinarith only [hm]
    _ = (∑h∈E.filter (fun h => a < mass weight (lines h)),mass weight (lines h))*
        Real.exp (-((R:ℝ)*(L:ℝ))*a) := by rw [Finset.sum_mul]
    _ ≤ M*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply le_trans _ hM
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun h _ _ => hmass h)

theorem heavy_empty_probability (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) {a M ε : ℝ} (hε : 0<ε)
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    (scheduleMeasure (fun i => L*weight i) R).real
      {ω | ε≤emptyWeight (E.filter fun h => a < mass weight (lines h)) lines
        (fun h => mass weight (lines h)) ω} ≤ M*Real.exp (-((R:ℝ)*(L:ℝ))*a)/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]
  apply (mul_meas_ge_le_integral_of_nonneg _
    (integrable_emptyWeight (fun i => L*weight i) _ _ _) ε).trans
    (heavy_empty_mean L weight E lines hM)
  exact Filter.Eventually.of_forall fun ω => emptyWeight_nonneg _ _ _
    (fun h _ => Finset.sum_nonneg fun i _ => (weight i).coe_nonneg) ω

end SharpRamseyFive.PoissonScore

end OAI
