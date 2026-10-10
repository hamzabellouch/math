import Mathlib
import OAI.Probability.SKValue.GroundState.QuadraticSK

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω : Type*} [MeasurableSpace Ω]

lemma empiricalVector_measurable (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun x : ℕ → Ω ↦ empiricalVector f x n) := by
  have hm : Measurable (fun x : ℕ → Ω ↦ WithLp.toLp 2 (fun i : Fin n ↦ f (x i))) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact hf.comp (measurable_pi_apply i.val)
  exact hm.const_smul (Real.sqrt (n : ℝ))⁻¹

lemma iid_average_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x : ℕ → Ω ↦ (∑ i∈Finset.range n,f (x i))/(n : ℝ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i hi
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).integrable_comp_of_integrable hf

lemma iid_average_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) {n : ℕ} (hn : 0<n) :
    (∫ x : ℕ → Ω,(∑ i∈Finset.range n,f (x i))/(n : ℝ)
      ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,f y ∂μ := by
  have hh (i : ℕ) : (∫ x : ℕ → Ω,f (x i) ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,f y ∂μ :=
    (iid_sample_law μ i).integral_comp hf.aestronglyMeasurable
  rw [integral_div,integral_finsetSum]
  · simp only [hh,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')
  · intro i hi
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).integrable_comp_of_integrable hf

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_sq (f : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) :
    ‖empiricalVector f x n‖^2=(∑ i∈Finset.range n,(f (x i))^2)/(n : ℝ) := by
  rw [←real_inner_self_eq_norm_sq,empiricalVector_inner]
  simp only [sq]

lemma empirical_norm_sq_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable (fun y ↦ (f y)^2) μ) (n : ℕ) :
    Integrable (fun x : ℕ → Ω ↦ ‖empiricalVector f x n‖^2)
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  simpa only [empiricalVector_norm_sq] using iid_average_integrable μ _ hf n

lemma empirical_norm_sq_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable (fun y ↦ (f y)^2) μ) {n : ℕ} (hn : 0<n) :
    (∫ x : ℕ → Ω,‖empiricalVector f x n‖^2
      ∂Measure.infinitePi (fun _ : ℕ ↦ μ))=∫ y,(f y)^2 ∂μ := by
  simpa only [empiricalVector_norm_sq] using iid_average_integral μ _ hf hn

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_unit (f : Ω → ℝ) (hf : ∀ y,(f y)^2=1)
    (x : ℕ → Ω) {n : ℕ} (hn : 0<n) : ‖empiricalVector f x n‖=1 := by
  have he : ‖empiricalVector f x n‖^2=1 := by
    rw [empiricalVector_norm_sq]
    simp only [hf,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    exact div_self (by exact_mod_cast hn.ne')
  nlinarith [norm_nonneg (empiricalVector f x n)]

omit [MeasurableSpace Ω] in
lemma empiricalVector_norm_le_one (f : Ω → ℝ) (hf : ∀ y,(f y)^2=1)
    (x : ℕ → Ω) (n : ℕ) : ‖empiricalVector f x n‖≤1 := by
  rcases n.eq_zero_or_pos with rfl|hn
  · simp [empiricalVector]
  · exact (empiricalVector_norm_unit f hf x hn).le

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma orthogonalRemainder_gramSchmidt_norm_le {κ : Type*} [Fintype κ]
    (a : ℕ → EuclideanSpace ℝ κ) (w : EuclideanSpace ℝ κ) (j : ℕ) :
    ‖orthogonalRemainder (gramSchmidtNormed ℝ a) w j‖≤‖w‖ := by
  induction j with
  | zero => simp [orthogonalRemainder]
  | succ j ih =>
    rw [←columnResidual_orthogonalRemainder _ _ _ (fun i hi ↦
      gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi)))]
    exact (columnResidual_norm_le (gramSchmidtNormed_unitOrZero a j) _).trans ih

lemma measurable_orthogonalRemainder {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (v : Ω → ℕ → EuclideanSpace ℝ κ) (w : Ω → EuclideanSpace ℝ κ)
    (hv : ∀ i,Measurable (fun x ↦ v x i)) (hw : Measurable w) (j : ℕ) :
    Measurable (fun x ↦ orthogonalRemainder (v x) (w x) j) := by
  unfold orthogonalRemainder
  apply hw.sub
  apply Finset.measurable_sum
  intro i hi
  have hi : Measurable (fun x ↦ (⟪v x i,w x⟫ : ℝ)) := (hv i).inner hw
  exact hi.smul (hv i)

lemma empiricalColumnEnergy_measurable (K n : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i)) (hF : Measurable F) (j : ℕ) :
    Measurable (fun x ↦ empiricalColumnEnergy K n f x F j) := by
  have ha (i : ℕ) := measurable_gramSchmidtNormed
    (fun x l ↦ empiricalVector (f l) x n) (fun l ↦ empiricalVector_measurable (f l) (hm l) n) i
  have hw := empiricalVector_measurable F hF n
  apply (measurable_columnVector (ha j)
    (measurable_orthogonalRemainder _ _ ha hw j)).inner
  apply empiricalVector_measurable
  split_ifs <;> fun_prop

lemma empiricalColumnEnergy_bound (K n : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hF : ∀ y,(F y)^2=1) (x : ℕ → (Fin (K+1) → ℝ)) {j : ℕ} (hj : j<K) :
    |empiricalColumnEnergy K n f x F j|≤
      1+‖empiricalVector (fun y ↦ y ⟨j+1,by omega⟩) x n‖^2 := by
  let a := fun l ↦ empiricalVector (f l) x n
  let w := empiricalVector F x n
  let z := empiricalVector (fun y ↦ y ⟨j+1,by omega⟩) x n
  have hw : ‖orthogonalRemainder (gramSchmidtNormed ℝ a) w j‖≤1 :=
    (orthogonalRemainder_gramSchmidt_norm_le a w j).trans
      (empiricalVector_norm_le_one F hF x n)
  have hc : ‖columnVector (gramSchmidtNormed ℝ a j)
      (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)‖≤1 :=
    (columnVector_norm_le (gramSchmidtNormed_unitOrZero a j) _).trans
      (by nlinarith [norm_nonneg (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)])
  unfold empiricalColumnEnergy
  simp only [dite_eq_left (show j+1<K+1 by omega)]
  calc
    _ ≤ ‖columnVector (gramSchmidtNormed ℝ a j)
        (orthogonalRemainder (gramSchmidtNormed ℝ a) w j)‖*‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]
    _ ≤ 1+‖z‖^2 := by nlinarith [sq_nonneg (‖z‖-1)]

end SKValueG

end

end OAI
