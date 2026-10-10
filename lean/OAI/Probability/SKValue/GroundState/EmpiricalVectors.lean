import Mathlib
import OAI.Probability.SKValue.GroundState.RandomColumn

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω : Type*}

noncomputable def empiricalVector (f : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i : Fin n ↦ f (x i))

lemma empiricalVector_inner (f g : Ω → ℝ) (x : ℕ → Ω) (n : ℕ) :
    ⟪empiricalVector f x n,empiricalVector g x n⟫=
      (∑ i∈Finset.range n,f (x i)*g (x i))/(n : ℝ) := by
  rw [empiricalVector,empiricalVector,real_inner_smul_left,real_inner_smul_right,
    euclidean_inner_sum]
  change (Real.sqrt (n : ℝ))⁻¹*((Real.sqrt (n : ℝ))⁻¹*
    ∑ i : Fin n,f (x i)*g (x i)) = _
  rw [←Fin.sum_univ_eq_sum_range]
  have hs : Real.sqrt (n : ℝ)^2=(n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  calc
    _ = (∑ i : Fin n,f (x i)*g (x i))/(Real.sqrt (n : ℝ))^2 := by ring
    _ = _ := by rw [hs]

variable [MeasurableSpace Ω]

lemma iid_sample_law (μ : Measure Ω) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun x : ℕ → Ω ↦ x i) μ (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).hasLaw

lemma iid_prefix_law (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    HasLaw (fun x : ℕ → Ω ↦ fun i : Fin n ↦ x i) (Measure.pi (fun _ : Fin n ↦ μ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply iIndepFun.hasLaw_pi (fun i : Fin n ↦ iid_sample_law μ i.val)
  exact (iIndepFun_infinitePi (P:=fun _ : ℕ ↦ μ) (X:=fun _ x ↦ x)
    (fun _ ↦ measurable_id)).precomp Fin.val_injective

lemma iid_average_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hm : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ (∑ i∈Finset.range n,f (x i))/(n : ℝ)) atTop (𝓝 (∫ y,f y ∂μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → Ω) ↦ f (x i)
  have hl (i : ℕ) : HasLaw (X i) (Measure.map f μ) P := (show HasLaw f (Measure.map f μ) μ from ⟨hm.aemeasurable,rfl⟩).comp (iid_sample_law μ i)
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ hm)
  have hi' : Integrable (X 0) P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).integrable_comp_of_integrable hi
  have he : (∫ x,X 0 x ∂P)=∫ y,f y ∂μ := (iid_sample_law μ 0).integral_comp hi.aestronglyMeasurable
  simpa only [X,he] using strong_law_ae_real X hi'
    (fun i j hij ↦ hind.indepFun hij) (fun i ↦ (hl i).identDistrib (hl 0))

lemma empirical_inner_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hm : Measurable (fun x ↦ f x*g x))
    (hi : Integrable (fun x ↦ f x*g x) μ) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ ⟪empiricalVector f x n,empiricalVector g x n⟫) atTop
        (𝓝 (∫ y,f y*g y ∂μ)) := by
  simpa only [empiricalVector_inner] using iid_average_tendsto μ (fun x ↦ f x*g x) hm hi

lemma empirical_norm_tendsto_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hm : Measurable f) (hi : Integrable (fun x ↦ (f x)^2) μ)
    (he : (∫ x,(f x)^2 ∂μ)=1) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n ↦ ‖empiricalVector f x n‖) atTop (𝓝 1) := by
  have hi' : Integrable (fun x ↦ f x*f x) μ := by simpa only [sq] using hi
  filter_upwards [empirical_inner_tendsto μ f f (hm.mul hm) hi'] with x hx
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hx
  simp only [←sq,he,Real.sqrt_one] at hh
  convert hh using 1
  ext n
  simp only [Function.comp_apply,real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma gramSchmidt_congr_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℕ → E) (j : ℕ) (h : ∀ i≤j,f i=g i) :
    gramSchmidt ℝ f j=gramSchmidt ℝ g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [gramSchmidt_eq_sub_sum_nat,gramSchmidt_eq_sub_sum_nat,h j le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij := Finset.mem_range.mp hi
    rw [ih i hij (fun l hl ↦ h l (by omega))]

lemma gramSchmidtNormed_congr_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℕ → E) (j : ℕ) (h : ∀ i≤j,f i=g i) :
    gramSchmidtNormed ℝ f j=gramSchmidtNormed ℝ g j := by
  simp only [gramSchmidtNormed,gramSchmidt_congr_prefix f g j h]

variable (K n : ℕ)

def paddedRow {j : ℕ} (h : ColumnHistory (Fin n) j) (i : Fin n) : Fin (K+1) → ℝ :=
  fun l ↦ if hl : l.val<j then h ⟨l.val,hl⟩ i else 0

lemma paddedRow_measurable (j : ℕ) (i : Fin n) :
    Measurable (fun h : ColumnHistory (Fin n) j ↦ paddedRow K n h i) := by
  unfold paddedRow
  apply Measurable.of_eval
  intro l
  split_ifs <;> fun_prop

noncomputable def rawHistory (f : ℕ → (Fin (K+1) → ℝ) → ℝ) {j : ℕ}
    (h : ColumnHistory (Fin n) j) (l : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i ↦ f l (paddedRow K n h i))

lemma rawHistory_measurable (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hf : ∀ l,Measurable (f l)) (j l : ℕ) :
    Measurable (fun h : ColumnHistory (Fin n) j ↦ rawHistory K n f h l) := by
  have hm : Measurable (fun h : ColumnHistory (Fin n) j ↦
      WithLp.toLp 2 (fun i : Fin n ↦ f l (paddedRow K n h i))) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact (hf l).comp (paddedRow_measurable K n j i)
  exact hm.const_smul (Real.sqrt (n : ℝ))⁻¹

noncomputable def predictableDirection (f : ℕ → (Fin (K+1) → ℝ) → ℝ) :
    (j : ℕ) → ColumnHistory (Fin n) j → EuclideanSpace ℝ (Fin n)
  | 0,_ => 0
  | j+1,h => gramSchmidtNormed ℝ (rawHistory K n f h) j

lemma predictableDirection_measurable (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hf : ∀ l,Measurable (f l)) (j : ℕ) : Measurable (predictableDirection K n f j) := by
  cases j with
  | zero => exact measurable_const
  | succ j => exact measurable_gramSchmidtNormed _ (rawHistory_measurable K n f hf (j+1)) j

lemma predictableDirection_unitOrZero (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (j : ℕ) (h : ColumnHistory (Fin n) j) :
    predictableDirection K n f j h=0 ∨
      ⟪predictableDirection K n f j h,predictableDirection K n f j h⟫=1 := by
  cases j with
  | zero => exact Or.inl rfl
  | succ j => exact gramSchmidtNormed_unitOrZero _ _

def rowColumn (x : Fin n → Fin (K+1) → ℝ) (j : ℕ) (i : Fin n) : ℝ :=
  if hj : j<K+1 then x i ⟨j,hj⟩ else 0

def rowHistory (x : Fin n → Fin (K+1) → ℝ) (j : ℕ) : ColumnHistory (Fin n) j :=
  fun l ↦ rowColumn K n x l.val

lemma rowHistory_init (x : Fin n → Fin (K+1) → ℝ) (j : ℕ) :
    historyInit (Fin n) (rowHistory K n x (j+1))=rowHistory K n x j := rfl

lemma rawHistory_rows (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (x : Fin n → Fin (K+1) → ℝ) (j l : ℕ) (hl : l<j) :
    rawHistory K n f (rowHistory K n x j) l=
      (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i ↦ f l (x i)) := by
  unfold rawHistory
  congr 1
  congr 1
  funext i
  apply ha
  intro k hk
  simp only [paddedRow,rowHistory,rowColumn]
  rw [dite_eq_left (show k.val<j by omega),dite_eq_left k.isLt]

lemma predictableDirection_rows (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (x : ℕ → (Fin (K+1) → ℝ)) (j : ℕ) :
    predictableDirection K n f (j+1) (rowHistory K n (fun i ↦ x i) (j+1))=
      gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j := by
  apply gramSchmidtNormed_congr_prefix
  intro l hl
  exact rawHistory_rows K n f ha _ _ _ (by omega)

end SKValueG

end

end OAI
