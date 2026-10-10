import Mathlib
import OAI.Probability.ParisiFinite.Field

namespace OAI

/-! Law. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory

namespace SKQAOA.GaussianEdge

abbrev law : Measure ℝ := gaussianReal 0 1

lemma integral_sq : ∫x:ℝ, x^2 ∂law = 1 := by
  have h := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (X:=fun x:ℝ => x) (show AEMeasurable (fun x:ℝ => x) (gaussianReal 0 1) from measurable_id.aemeasurable)] at h
  simpa [integral_id_gaussianReal] using h

lemma integrable_sq : Integrable (fun x:ℝ => x^2) law :=
  (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq

lemma integral_neg_comp (f : ℝ → ℝ) : (∫x, f (-x) ∂law) = ∫x, f x ∂law := by
  have h : MeasurePreserving (fun x:ℝ => -x) law law :=
    ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ:=0) (v:=1))⟩
  exact h.integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding f

lemma integral_zero_of_odd (f : ℝ → ℝ) (h : ∀x, f (-x) = -f x) :
    (∫x, f x ∂law)=0 := by
  have he := integral_neg_comp f
  simp_rw [h] at he
  rw [integral_neg] at he
  linarith

lemma integral_sq_bound (f : ℝ → ℝ) (hf : Continuous f) {C : ℝ}
    (_hC : 0 ≤ C) (hb : ∀x, |f x| ≤ C*x^2) : |∫x, f x ∂law| ≤ C := by
  have hi : Integrable f law := (integrable_sq.const_mul C).mono'
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (by simpa using hb))
  calc
    |∫x, f x ∂law| ≤ ∫x, |f x| ∂law := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ ∫x:ℝ, C*x^2 ∂law := integral_mono hi.abs (integrable_sq.const_mul C) hb
    _ = C := by rw [integral_const_mul, integral_sq, mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 

def trigWord (θ : ι → ℝ) (S : Finset ι) (x : ℝ) : ℝ :=
  (∏i∈S, Real.sin (θ i*x)) * ∏i∈Sᶜ, Real.cos (θ i*x)

lemma continuous_trigWord (θ : ι → ℝ) (S : Finset ι) : Continuous (trigWord θ S) := by
  unfold trigWord
  fun_prop

lemma trigWord_neg (θ : ι → ℝ) (S : Finset ι) (x : ℝ) :
    trigWord θ S (-x) = (-1)^S.card*trigWord θ S x := by
  simp only [trigWord, mul_neg, Real.sin_neg, Real.cos_neg, Finset.prod_neg]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma abs_prod_le_one {s : Finset ι} {f : ι → ℝ} (h : ∀i∈s, |f i| ≤ 1) :
    |∏i∈s, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  exact (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) h)

lemma abs_trigWord_le_one (θ : ι → ℝ) (S : Finset ι) (x : ℝ) :
    |trigWord θ S x| ≤ 1 := by
  rw [trigWord, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _)
    (abs_prod_le_one (by intros; exact Real.abs_sin_le_one _))).trans
    (abs_prod_le_one (by intros; exact Real.abs_cos_le_one _))

 
lemma abs_trigWord_le_subpattern (θ : ι → ℝ) {T S : Finset ι}
    (hTS : T ⊆ S) (x : ℝ) : |trigWord θ S x| ≤ ∏i∈T, |Real.sin (θ i*x)| := by
  calc
    |trigWord θ S x| ≤ |∏i∈S, Real.sin (θ i*x)| := by
      rw [trigWord, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_prod_le_one (by intros; exact Real.abs_cos_le_one _))
    _ ≤ ∏i∈T, |Real.sin (θ i*x)| := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod_of_subset_of_le_one₀ hTS
        (by intros; exact abs_nonneg _) (by intros; exact Real.abs_sin_le_one _)

lemma abs_trigWord_le_one_sine (θ : ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i∈S) (x : ℝ) : |trigWord θ S x| ≤ |θ i| *|x| := by
  calc
    _ ≤ |Real.sin (θ i*x)| := by
      simpa using abs_trigWord_le_subpattern θ (Finset.singleton_subset_iff.mpr hi) x
    _ ≤ |θ i| *|x| := by simpa [abs_mul] using (Real.abs_sin_le_abs (x:=θ i*x))

lemma abs_trigWord_le_two_sines (θ : ι → ℝ) {S : Finset ι} {i j : ι}
    (hi : i∈S) (hj : j∈S) (hij : i≠j) (x : ℝ) :
    |trigWord θ S x| ≤ (|θ i| *|θ j|)*x^2 := by
  calc
    _ ≤ |Real.sin (θ i*x)| *|Real.sin (θ j*x)| := by
      simpa [hij] using abs_trigWord_le_subpattern θ
        (show {i,j} ⊆ S by intro k hk; rcases Finset.mem_insert.mp hk with rfl | hk; exact hi; obtain rfl := Finset.mem_singleton.mp hk; exact hj) x
    _ ≤ (|θ i| *|x|) * (|θ j| *|x|) := mul_le_mul
      (by simpa [abs_mul] using (Real.abs_sin_le_abs (x:=θ i*x)))
      (by simpa [abs_mul] using (Real.abs_sin_le_abs (x:=θ j*x)))
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (|θ i| *|θ j|)*x^2 := by rw [show x^2=|x|^2 by simp]; ring

omit [Fintype ι] in
lemma abs_prod_sub_one_le (s : Finset ι) (f : ι → ℝ)
    (hf : ∀i∈s, |f i| ≤ 1) : |(∏i∈s, f i)-1| ≤ ∑i∈s, |f i-1| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      |f a*(∏i∈s,f i)-1| = |f a*((∏i∈s,f i)-1)+(f a-1)| := by congr 1; ring
      _ ≤ |f a*((∏i∈s,f i)-1)|+|f a-1| := abs_add_le _ _
      _ ≤ |(∏i∈s,f i)-1|+|f a-1| := by
        rw [abs_mul]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hf a (by simp))) le_rfl
      _ ≤ (∑i∈s,|f i-1|)+|f a-1| := add_le_add (ih (by aesop)) le_rfl
      _ = |f a-1|+∑i∈s,|f i-1| := add_comm _ _

lemma abs_cos_sub_one_le_sq (x : ℝ) : |Real.cos x-1| ≤ x^2/2 := by
  have hs := Real.abs_sin_le_abs (x:=x/2)
  have hs2 : (Real.sin (x/2))^2 ≤ (x/2)^2 := by
    nlinarith [sq_abs (Real.sin (x/2)),sq_abs (x/2),abs_nonneg (Real.sin (x/2)),abs_nonneg (x/2)]
  have hc := Real.cos_two_mul_eq_one_sub (x/2)
  rw [show (2:ℝ)*(x/2)=x by ring] at hc
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
  nlinarith

lemma abs_trigWord_empty_sub_one (θ : ι → ℝ) (x : ℝ) :
    |trigWord θ ∅ x-1| ≤ ((∑i, θ i^2)/2)*x^2 := by
  simp only [trigWord,Finset.prod_empty,one_mul,Finset.compl_empty]
  calc
    _ ≤ ∑i, |Real.cos (θ i*x)-1| :=
      abs_prod_sub_one_le _ _ (by intros; exact Real.abs_cos_le_one _)
    _ ≤ ∑i, (θ i*x)^2/2 := Finset.sum_le_sum (by intros; exact abs_cos_sub_one_le_sq _)
    _ = ((∑i, θ i^2)/2)*x^2 := by
      simp_rw [mul_pow,div_eq_mul_inv]
      rw [←Finset.sum_mul,←Finset.sum_mul]
      ring

 
lemma integral_trigWord_odd (θ : ι → ℝ) (S : Finset ι) (hS : Odd S.card) :
    (∫x, trigWord θ S x ∂law)=0 := by
  apply integral_zero_of_odd
  intro x
  rw [trigWord_neg,hS.neg_one_pow]
  ring

 
lemma integral_marked_trigWord_even (θ : ι → ℝ) (S : Finset ι) (hS : Even S.card) :
    (∫x, x*trigWord θ S x ∂law)=0 := by
  apply integral_zero_of_odd
  intro x
  rw [trigWord_neg,hS.neg_one_pow]
  ring

lemma integral_trigWord_two_sines (θ : ι → ℝ) {S : Finset ι} {i j : ι}
    (hi : i∈S) (hj : j∈S) (hij : i≠j) :
    |∫x, trigWord θ S x ∂law| ≤ |θ i| *|θ j| :=
  integral_sq_bound _ (continuous_trigWord θ S) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (abs_trigWord_le_two_sines θ hi hj hij)

lemma integral_marked_trigWord_one_sine (θ : ι → ℝ) {S : Finset ι} {i : ι}
    (hi : i∈S) : |∫x, x*trigWord θ S x ∂law| ≤ |θ i| := by
  apply integral_sq_bound _ (continuous_id.mul (continuous_trigWord θ S)) (abs_nonneg _)
  intro x
  calc
    |x*trigWord θ S x| ≤ |x| *(|θ i| *|x|) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_trigWord_le_one_sine θ hi x) (abs_nonneg _)
    _ = |θ i| *x^2 := by rw [show x^2=|x|^2 by simp]; ring

 
lemma integral_trigWord_empty_sub_one (θ : ι → ℝ) :
    |∫x, (trigWord θ ∅ x-1) ∂law| ≤ (∑i, θ i^2)/2 :=
  integral_sq_bound _ ((continuous_trigWord θ ∅).sub continuous_const)
    (div_nonneg (Finset.sum_nonneg (by intros; positivity)) (by norm_num))
    (abs_trigWord_empty_sub_one θ)

end SKQAOA.GaussianEdge

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace ClassicalGaussian

theorem integrable_real_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (r : ℕ) (hf : MemLp f r μ) :
    Integrable (fun x => f x^r) μ := by
  apply hf.integrable_norm_pow'.mono' (hf.aestronglyMeasurable.pow r)
  exact Filter.Eventually.of_forall (fun x => le_of_eq (norm_pow _ _))

theorem integrable_standard_pow (r : ℕ) :
    Integrable (fun x : ℝ => x^r) (gaussianReal 0 1) := by
  apply integrable_real_pow r
  exact memLp_id_gaussianReal' _ (by simp)

 

theorem standard_fourth : (∫x : ℝ,x^4 ∂gaussianReal 0 1)=3 := by
  have h := SKGaussian.integral_mul_eq_integral_deriv
    (f:=fun x : ℝ=>x^3) (f':=fun x : ℝ=>3*x^2)
    (fun x => by simpa using (hasDerivAt_id x).fun_pow 3)
    (integrable_standard_pow 3) ((integrable_standard_pow 2).const_mul 3)
    (by convert integrable_standard_pow 4 using 1; funext x; ring)
  have he : (fun x : ℝ=>x*x^3)=(fun x : ℝ=>x^4) := by funext x; ring
  rw [he,integral_const_mul,SKQAOA.GaussianEdge.integral_sq,mul_one] at h
  exact h

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memLp_field_nat (d : E) (r : ℕ) : MemLp (field E d) r (stdGaussian E) := by
  exact (innerSL ℝ d).comp_memLp' (IsGaussian.memLp_id (stdGaussian E) r (by simp))

theorem integrable_field_pow (d : E) (r : ℕ) :
    Integrable (fun g => field E d g^r) (stdGaussian E) :=
  integrable_real_pow r (memLp_field_nat E d r)

 

theorem field_fourth (d : E) : (∫g,field E d g^4 ∂stdGaussian E)=3*‖d‖^4 := by
  have hf : HasLaw (field E d) (gaussianReal 0 (‖d‖₊^2)) (stdGaussian E) :=
    ⟨by unfold field; fun_prop,field_law E d⟩
  have hs : HasLaw (fun x : ℝ => ‖d‖*x) (gaussianReal 0 (‖d‖₊^2))
      (gaussianReal 0 1) := by
    refine ⟨by fun_prop,?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.coe_injective
      simp [pow_two]
  calc
    _ = ∫x : ℝ,x^4 ∂gaussianReal 0 (‖d‖₊^2) :=
      hf.integral_comp (by fun_prop)
    _ = ∫x : ℝ,(‖d‖*x)^4 ∂gaussianReal 0 1 :=
      (hs.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^4)
        (gaussianReal 0 (‖d‖₊^2)))).symm
    _ = 3*‖d‖^4 := by
      simp only [mul_pow,integral_const_mul,standard_fourth]
      ring

end ClassicalGaussian

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace ClassicalGaussian
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem field_add (d e : E) (g : E) :
    field E (d+e) g=field E d g+field E e g := by
  simp [field,inner_add_left]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem field_sub (d e : E) (g : E) :
    field E (d-e) g=field E d g-field E e g := by
  simp [field,inner_sub_left]

theorem memLp_field_product (d e : E) :
    MemLp (fun g=>field E d g*field E e g) 2 (stdGaussian E) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact (memLp_field_nat E d 4).fun_mul (memLp_field_nat E e 4)

theorem integrable_field_four (a b c d : E) :
    Integrable (fun g=>field E a g*field E b g*(field E c g*field E d g))
      (stdGaussian E) :=
  (memLp_field_product E a b).integrable_mul (memLp_field_product E c d)

private theorem polarization (a b c d : ℝ) :
    192*(a*b*(c*d)) =
    (a+b+c+d)^4-(a+b+c-d)^4-(a+b-c+d)^4+(a+b-c-d)^4
    -(a-b+c+d)^4+(a-b+c-d)^4+(a-b-c+d)^4-(a-b-c-d)^4 := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem fourth_norm (d : E) : ‖d‖^4=⟪d,d⟫^2 := by
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,real_inner_self_eq_norm_sq]

 

theorem field_wick_four (a b c d : E) :
    (∫g,field E a g*field E b g*(field E c g*field E d g) ∂stdGaussian E)=
      ⟪a,b⟫*⟪c,d⟫+⟪a,c⟫*⟪b,d⟫+⟪a,d⟫*⟪b,c⟫ := by
  have he : (fun g=>192*(field E a g*field E b g*(field E c g*field E d g))) =
      (fun g=>field E (a+b+c+d) g^4-field E (a+b+c-d) g^4-
        field E (a+b-c+d) g^4+field E (a+b-c-d) g^4-
        field E (a-b+c+d) g^4+field E (a-b+c-d) g^4+
        field E (a-b-c+d) g^4-field E (a-b-c-d) g^4) := by
    funext g
    simp only [field_add,field_sub]
    exact polarization _ _ _ _
  have h := congrArg (fun f : E → ℝ=>∫g,f g ∂stdGaussian E) he
  rw [integral_const_mul] at h
  have h2 := (integrable_field_pow E (a+b+c+d) 4).sub
    (integrable_field_pow E (a+b+c-d) 4)
  have h3 := h2.sub (integrable_field_pow E (a+b-c+d) 4)
  have h4 := h3.add (integrable_field_pow E (a+b-c-d) 4)
  have h5 := h4.sub (integrable_field_pow E (a-b+c+d) 4)
  have h6 := h5.add (integrable_field_pow E (a-b+c-d) 4)
  have h7 := h6.add (integrable_field_pow E (a-b-c+d) 4)
  have hs8 := integral_sub h7 (integrable_field_pow E (a-b-c-d) 4)
  have hs7 := integral_add h6 (integrable_field_pow E (a-b-c+d) 4)
  have hs6 := integral_add h5 (integrable_field_pow E (a-b+c-d) 4)
  have hs5 := integral_sub h4 (integrable_field_pow E (a-b+c+d) 4)
  have hs4 := integral_add h3 (integrable_field_pow E (a+b-c-d) 4)
  have hs3 := integral_sub h2 (integrable_field_pow E (a+b-c+d) 4)
  have hs2 := integral_sub (integrable_field_pow E (a+b+c+d) 4)
    (integrable_field_pow E (a+b+c-d) 4)
  simp only [Pi.sub_apply,Pi.add_apply] at hs8 hs7 hs6 hs5 hs4 hs3 hs2
  rw [hs8,hs7,hs6,hs5,hs4,hs3,hs2] at h
  simp only [field_fourth,fourth_norm] at h
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at h
  simp only [real_inner_comm] at h ⊢
  linear_combination h / 192

end ClassicalGaussian

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace ClassicalGaussian
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

def centeredQuadratic (d e : E) (g : E) : ℝ :=
  field E d g*field E e g-⟪d,e⟫

theorem memLp_centeredQuadratic (d e : E) :
    MemLp (centeredQuadratic E d e) 2 (stdGaussian E) :=
  (memLp_field_product E d e).sub (memLp_const _)

theorem integral_centeredQuadratic (d e : E) :
    (∫g,centeredQuadratic E d e g ∂stdGaussian E)=0 := by
  simp only [centeredQuadratic]
  have hs := integral_sub ((memLp_field E d).integrable_mul
    (memLp_field E e)) (integrable_const (⟪d,e⟫))
  simp only [Pi.mul_apply] at hs
  rw [hs,field_covariance]
  simp

theorem covariance_centeredQuadratic (a b c d : E) :
    (∫g,centeredQuadratic E a b g*centeredQuadratic E c d g ∂stdGaussian E)=
      ⟪a,c⟫*⟪b,d⟫+⟪a,d⟫*⟪b,c⟫ := by
  have he : (fun g=>centeredQuadratic E a b g*centeredQuadratic E c d g)=
      (fun g=>field E a g*field E b g*(field E c g*field E d g)-
        ⟪c,d⟫*(field E a g*field E b g)-
        ⟪a,b⟫*(field E c g*field E d g)+⟪a,b⟫*⟪c,d⟫) := by
    funext g
    unfold centeredQuadratic
    ring
  rw [he]
  have hab := (memLp_field E a).integrable_mul (memLp_field E b)
  have hcd := (memLp_field E c).integrable_mul (memLp_field E d)
  have h4 := integrable_field_four E a b c d
  have hs3 := integral_add ((h4.sub (hab.const_mul ⟪c,d⟫)).sub
    (hcd.const_mul ⟪a,b⟫)) (integrable_const (⟪a,b⟫*⟪c,d⟫))
  have hs2 := integral_sub (h4.sub (hab.const_mul ⟪c,d⟫)) (hcd.const_mul ⟪a,b⟫)
  have hs1 := integral_sub h4 (hab.const_mul ⟪c,d⟫)
  simp only [Pi.sub_apply,Pi.mul_apply] at hs3 hs2 hs1
  rw [hs3,hs2,hs1]
  simp only [integral_const_mul,field_covariance,field_wick_four,integral_const,
    probReal_univ,one_smul]
  ring

 

theorem quadratic_sum_variance {ι : Type*} (s : Finset ι) (d e : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0) :
    (∫g,(∑i∈s,centeredQuadratic E (d i) (e i) g)^2 ∂stdGaussian E)=
      ∑i∈s,(‖d i‖^2*‖e i‖^2+⟪d i,e i⟫^2) := by
  have hi (i j : ι) : Integrable
      (fun g=>centeredQuadratic E (d i) (e i) g*
        centeredQuadratic E (d j) (e j) g) (stdGaussian E) :=
    (memLp_centeredQuadratic E _ _).integrable_mul (memLp_centeredQuadratic E _ _)
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i his
    rw [integral_finsetSum]
    · simp only [covariance_centeredQuadratic]
      rw [Finset.sum_eq_single i]
      · simp only [real_inner_self_eq_norm_sq,real_inner_comm (e i) (d i)]
        ring
      · intro j hjs hji
        rcases ho j hjs i his hji with ⟨hdd,hde⟩
        simp [hdd,hde]
      · simp [his]
    · intro j hjs
      exact hi j i
  · intro i his
    exact integrable_finsetSum _ (fun j hjs=>hi j i)

 

theorem quadratic_sum_variance_le {ι : Type*} (s : Finset ι) (d e : ι → E)
    (p : ι → ℝ) (C : ℝ) (hC : 0≤C) (hp : ∀i∈s,0≤p i)
    (hd : ∀i∈s,‖d i‖^2≤C*p i) (he : ∀i∈s,‖e i‖^2≤C*p i)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0) :
    (∫g,(∑i∈s,centeredQuadratic E (d i) (e i) g)^2 ∂stdGaussian E)≤
      2*C^2*∑i∈s,(p i)^2 := by
  rw [quadratic_sum_variance E s d e ho,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i his
  have hc : ⟪d i,e i⟫^2≤‖d i‖^2*‖e i‖^2 := by
    have h := sq_le_sq₀ (abs_nonneg ⟪d i,e i⟫)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr (abs_real_inner_le_norm (d i) (e i))
    simpa only [sq_abs,mul_pow] using h
  have hm : ‖d i‖^2*‖e i‖^2≤(C*p i)^2 := by
    simpa only [pow_two] using mul_le_mul (hd i his) (he i his)
      (sq_nonneg _) (mul_nonneg hC (hp i his))
  nlinarith

end ClassicalGaussian

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace ClassicalGaussian

 

def phaseError (t x : ℝ) : ℝ :=
  ‖Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))-1‖^2

theorem phaseError_nonneg (t x : ℝ) : 0≤phaseError t x := sq_nonneg _

theorem continuous_phaseError (t : ℝ) : Continuous (phaseError t) := by
  unfold phaseError
  fun_prop

theorem phaseError_le_sq (t x : ℝ) : phaseError t x≤t^2*x^2 := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=t*x)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  simpa only [phaseError,Real.norm_eq_abs,sq_abs,mul_pow] using hsq

theorem phaseError_le_four (t x : ℝ) : phaseError t x≤4 := by
  have h : ‖Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))-1‖≤2 := by
    calc
      _≤‖Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _=2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num
  unfold phaseError
  have hn := norm_nonneg (Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))-1)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_phaseError {q : Ω → ℝ} (hq : MemLp q 2 μ) (t : ℝ) :
    Integrable (fun g=>phaseError t (q g)) μ := by
  apply ((integrable_real_pow 2 hq).const_mul (t^2)).mono'
    ((continuous_phaseError t).comp_aestronglyMeasurable hq.aestronglyMeasurable)
  exact Eventually.of_forall fun g=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (phaseError_nonneg _ _)]
    exact phaseError_le_sq _ _

 
theorem integral_phaseError_le {q : Ω → ℝ} (hq : MemLp q 2 μ) (t : ℝ) :
    (∫g,phaseError t (q g) ∂μ)≤t^2*∫g,q g^2 ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono (integrable_phaseError μ hq t)
    ((integrable_real_pow 2 hq).const_mul _) (fun _=>phaseError_le_sq _ _)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

theorem quadratic_phase_L2_le {ι : Type*} (s : Finset ι) (d e : ι → E)
    (p : ι → ℝ) (C : ℝ) (hC : 0≤C) (hp : ∀i∈s,0≤p i)
    (hd : ∀i∈s,‖d i‖^2≤C*p i) (he : ∀i∈s,‖e i‖^2≤C*p i)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0) (t : ℝ) :
    (∫g,phaseError t (∑i∈s,centeredQuadratic E (d i) (e i) g) ∂stdGaussian E)≤
      t^2*(2*C^2*∑i∈s,(p i)^2) := by
  apply le_trans (integral_phaseError_le (stdGaussian E) ?_ t)
  · exact mul_le_mul_of_nonneg_left (quadratic_sum_variance_le E s d e p C hC hp hd he ho)
      (sq_nonneg t)
  · exact memLp_finsetSum s (fun i hi=>memLp_centeredQuadratic E (d i) (e i))

end ClassicalGaussian

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace ClassicalGaussian
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

 

omit [IsFiniteMeasure μ] in
theorem weighted_bounded_integral_tendsto {f : ℕ → Ω → ℝ} (B : ℝ)
    (hf : ∀n,Integrable (f n) μ) (hn : ∀n x,0≤f n x) (hb : ∀n x,f n x≤B)
    (ht : Tendsto (fun n=>∫x,f n x ∂μ) atTop (𝓝 0))
    (ρ : Ω → ℝ) (hρ : Integrable ρ μ) :
    Tendsto (fun n=>∫x,|ρ x| *f n x ∂μ) atTop (𝓝 0) := by
  have he (n : ℕ) : eLpNorm (f n-(0:Ω → ℝ)) 1 μ=
      ENNReal.ofReal (∫x,f n x ∂μ) := by
    simp only [sub_zero]
    rw [eLpNorm_one_eq_lintegral_enorm (hf n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>Real.norm_of_nonneg (hn n x)
  have hp : TendstoInMeasure μ f atTop (0:Ω → ℝ) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p:=1) (by norm_num)
    simp_rw [he]
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp ht
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,_,hms⟩ := (hp.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hd := tendsto_integral_of_dominated_convergence
    (F:=fun n x=>|ρ x| *f (ns (ms n)) x) (f:=fun _ => (0:ℝ))
    (fun x=>|ρ x| *B)
    (fun n=>hρ.abs.aestronglyMeasurable.mul (hf _).aestronglyMeasurable)
    (hρ.abs.mul_const B) ?_ ?_
  · simpa only [integral_zero] using hd
  · intro n
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hn _ _))]
      exact mul_le_mul_of_nonneg_left (hb _ _) (abs_nonneg _)
  · filter_upwards [hms] with x hx
    simpa only [Pi.zero_apply,mul_zero,Function.comp_def] using hx.const_mul |ρ x|

 

theorem phase_weighted_L2_tendsto {q : ℕ → Ω → ℝ} (hq : ∀n,MemLp (q n) 2 μ)
    (ht : Tendsto (fun n=>∫x,q n x^2 ∂μ) atTop (𝓝 0)) (t : ℝ)
    (ρ : Ω → ℝ) (hρ : Integrable ρ μ) :
    Tendsto (fun n=>∫x,|ρ x| *phaseError t (q n x) ∂μ) atTop (𝓝 0) := by
  apply weighted_bounded_integral_tendsto μ 4
    (fun n=>integrable_phaseError μ (hq n) t)
    (fun _ _=>phaseError_nonneg _ _) (fun _ _=>phaseError_le_four _ _)
    ?_ ρ hρ
  apply squeeze_zero (fun n=>integral_nonneg (fun x=>phaseError_nonneg _ _))
    (fun n=>integral_phaseError_le μ (hq n) t)
  simpa only [mul_zero] using ht.const_mul (t^2)

 

theorem phase_vector_L2_tendsto {q : ℕ → Ω → ℝ} (hq : ∀n,MemLp (q n) 2 μ)
    (ht : Tendsto (fun n=>∫x,q n x^2 ∂μ) atTop (𝓝 0)) (t : ℝ)
    (ψ : Ω → ℂ) (hψ : MemLp ψ 2 μ) :
    Tendsto (fun n=>∫x,‖Complex.exp (Complex.I*((t*q n x : ℝ):ℂ))*ψ x-ψ x‖^2 ∂μ)
      atTop (𝓝 0) := by
  have hw := phase_weighted_L2_tendsto μ hq ht t (fun x=>‖ψ x‖^2)
    hψ.integrable_norm_pow'
  have he (n : ℕ) (x : Ω) :
      ‖Complex.exp (Complex.I*((t*q n x : ℝ):ℂ))*ψ x-ψ x‖^2=
      |‖ψ x‖^2| *phaseError t (q n x) := by
    rw [show Complex.exp (Complex.I*((t*q n x : ℝ):ℂ))*ψ x-ψ x=
      (Complex.exp (Complex.I*((t*q n x : ℝ):ℂ))-1)*ψ x by ring]
    rw [norm_mul,mul_pow,abs_of_nonneg (sq_nonneg _)]
    exact mul_comm _ _
  simp_rw [he]
  exact hw

end ClassicalGaussian

 

open scoped BigOperators TensorProduct

namespace OrthogonalKernels
variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

 
theorem norm_sum_sq (s : Finset ι) (d : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → inner 𝕜 (d i) (d j)=0) :
    ‖∑i∈s,d i‖^2=∑i∈s,‖d i‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hz : inner 𝕜 (d a) (∑i∈s,d i)=0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (by intro h; subst i; exact ha hi)
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hz
    simp only [←pow_two] at hh
    rw [Finset.sum_insert ha,Finset.sum_insert ha,hh,ih]
    intro i hi j hj hn
    exact ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hn

 

theorem tensor_sum_norm_sq (s : Finset ι) (d : ι → E) (e : ι → F)
    (ho : ∀i∈s,∀j∈s,i≠j → inner 𝕜 (d i) (d j)=0) :
    ‖∑i∈s,d i ⊗ₜ[𝕜] e i‖^2=∑i∈s,‖d i‖^2*‖e i‖^2 := by
  rw [norm_sum_sq (𝕜:=𝕜)]
  · simp only [TensorProduct.norm_tmul,mul_pow]
  · intro i hi j hj hn
    rw [TensorProduct.inner_tmul,ho i hi j hj hn,zero_mul]

 

theorem tensor_sum_norm_sq_le (s : Finset ι) (d : ι → E) (e : ι → F)
    (p : ι → ℝ) (C D : ℝ) (hC : 0≤C) (hp : ∀i∈s,0≤p i)
    (hd : ∀i∈s,‖d i‖^2≤C*p i) (he : ∀i∈s,‖e i‖^2≤D*p i)
    (ho : ∀i∈s,∀j∈s,i≠j → inner 𝕜 (d i) (d j)=0) :
    ‖∑i∈s,d i ⊗ₜ[𝕜] e i‖^2≤C*D*∑i∈s,(p i)^2 := by
  rw [tensor_sum_norm_sq s d e ho,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul (hd i hi) (he i hi) (sq_nonneg ‖e i‖)
    (mul_nonneg hC (hp i hi))
  nlinarith

 

theorem rankOne_sum_apply_sq_le (s : Finset ι) (d : ι → E) (e : ι → F)
    (ho : ∀i∈s,∀j∈s,i≠j → inner 𝕜 (d i) (d j)=0) (x : F) :
    ‖(∑i∈s,InnerProductSpace.rankOne 𝕜 (d i) (e i)) x‖^2≤
      (∑i∈s,‖d i‖^2*‖e i‖^2)*‖x‖^2 := by
  simp only [sum_apply,InnerProductSpace.rankOne_apply]
  rw [norm_sum_sq (𝕜:=𝕜),Finset.sum_mul]
  · apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul,mul_pow]
    have h := sq_le_sq₀ (norm_nonneg (inner 𝕜 (e i) x))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr (norm_inner_le_norm (e i) x)
    simp only [mul_pow] at h
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖d i‖)]
  · intro i hi j hj hn
    simp only [inner_smul_left,inner_smul_right,ho i hi j hj hn,mul_zero]

 

theorem rankOne_sum_norm_le (s : Finset ι) (d : ι → E) (e : ι → F)
    (ho : ∀i∈s,∀j∈s,i≠j → inner 𝕜 (d i) (d j)=0) :
    ‖∑i∈s,InnerProductSpace.rankOne 𝕜 (d i) (e i)‖≤
      Real.sqrt (∑i∈s,‖d i‖^2*‖e i‖^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have h := rankOne_sum_apply_sq_le s d e ho x
  have hs : 0≤∑i∈s,‖d i‖^2*‖e i‖^2 :=
    Finset.sum_nonneg (fun i hi=>mul_nonneg (sq_nonneg _) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hs] using h

end OrthogonalKernels

end

end OAI
