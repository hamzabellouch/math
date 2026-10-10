import Mathlib
import OAI.Probability.ParisiFinite.GramBlock

namespace OAI

/-! Selected Block. -/

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma selectedBlock_support {μ : ProbabilityMeasure OverlapArray} (hex : FiniteExchangeable μ)
    {r : ℕ} (e : Fin r → ℕ) (he : Function.Injective e) {R : OverlapArray}
    (hR : R∈(μ : Measure OverlapArray).support) : selectedBlock e R∈(blockLaw μ r).support := by
  rw [Measure.support_eq_forall_isOpen] at hR ⊢
  intro U hU hOpen
  have hh := hR ((selectedBlock e) ⁻¹' U) hU (hOpen.preimage (continuous_selectedBlock e))
  have hm := congrArg (fun ν : Measure (OverlapBlock r) => ν U) (hex r e he)
  rw [Measure.map_apply (continuous_selectedBlock e).measurable hOpen.measurableSet] at hm
  rwa [hm] at hh

lemma arraySupport_Gram {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) : (μ : Measure OverlapArray).support ⊆ GramArrays := by
  apply Measure.support_subset_of_isClosed isClosed_GramArrays
  apply ae_iff.mpr
  change (μ : Measure OverlapArray) GramArraysᶜ=0
  rw [measure_compl isClosed_GramArrays.measurableSet (measure_ne_top _ _),hG]
  simp

def UltrametricArrays : Set OverlapArray := {R | ∀ i j k : ℕ, min (R i k:ℝ) (R j k:ℝ)≤(R i j:ℝ)}

lemma isClosed_UltrametricArrays : IsClosed UltrametricArrays := by
  unfold UltrametricArrays
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)

 

theorem GG_support_ultrametric {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ) :
    (μ : Measure OverlapArray).support ⊆ UltrametricArrays := by
  intro R hR i j k
  have hg := arraySupport_Gram hG hR
  by_cases hij : i=j
  · subst j
    rw [hg.2.1 i,min_self]
    exact (R i k).2.2
  by_cases hik : i=k
  · subst k
    rw [hg.1 j i]
    exact min_le_right _ _
  by_cases hjk : j=k
  · subst k
    exact min_le_left _ _
  let e : Fin 3 → ℕ := ![i,j,k]
  have he : Function.Injective e := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [e]
  exact supported_triangle_ultrametric hG hgg hex (selectedBlock_support hex e he hR)

 

theorem GG_ultrametric {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ) :
    (μ : Measure OverlapArray) UltrametricArrays=1 := by
  apply le_antisymm prob_le_one
  calc
    1 = (μ : Measure OverlapArray) (μ : Measure OverlapArray).support := by
      have hs : (μ : Measure OverlapArray).support =ᵐ[(μ : Measure OverlapArray)] Set.univ := by
        filter_upwards [(μ : Measure OverlapArray).support_mem_ae] with R hR
        exact propext ⟨fun _ => Set.mem_univ R,fun _ => hR⟩
      rw [measure_congr hs,measure_univ]
    _ ≤ _ := measure_mono (GG_support_ultrametric hG hgg hex)

 

theorem exists_generic_ultrametric_limit (β : ℝ) :
    ∃ μ : ProbabilityMeasure OverlapArray,
      (μ : Measure OverlapArray) GramArrays=1 ∧ GGIdentities μ ∧ FiniteExchangeable μ ∧
      (μ : Measure OverlapArray) UltrametricArrays=1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ) := by
  obtain ⟨μ,φ,hφ,hμ⟩ := CompactSpace.tendsto_subseq (fun n => genericOverlapLaw n β)
  have hG := genericOverlap_limit_Gram β hφ hμ
  have hgg := genericOverlap_limit_GGIdentities β hφ hμ
  have hex := genericOverlap_limit_FiniteExchangeable β hφ hμ
  exact ⟨μ,hG,hgg,hex,GG_ultrametric hG hgg hex,φ,hφ,hμ⟩

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

lemma pow_sub_lipschitz_unit {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) (p : ℕ) :
    |a^p-b^p|≤(p:ℝ)*|a-b| := by
  have h := abs_pow_sub_pow_le a b p
  have hm : max |a| |b|≤1 := max_le ha hb
  have hp := pow_le_one₀ (le_max_of_le_left (abs_nonneg a)) hm (n:=p-1)
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ |a-b| * (p:ℝ))
  nlinarith only [h,hh]

lemma overlap_last_split {n : ℕ} (hn : 0 < n) (σ τ : Configuration (n+1)) :
    overlap σ τ=((n:ℝ)*overlap (restrictLeft σ) (restrictLeft τ)+
      spin σ (Fin.last n)*spin τ (Fin.last n))/(n+1) := by
  rw [overlap,overlapSum_last,overlap]
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  field_simp

lemma overlap_restrict_difference {n : ℕ} (hn : 0 < n) (σ τ : Configuration (n+1)) :
    |overlap σ τ-overlap (restrictLeft σ) (restrictLeft τ)|≤2/((n:ℝ)+1) := by
  rw [overlap_last_split hn]
  have he : ((n:ℝ)*overlap (restrictLeft σ) (restrictLeft τ)+
      spin σ (Fin.last n)*spin τ (Fin.last n))/(n+1)-overlap (restrictLeft σ) (restrictLeft τ)=
      (spin σ (Fin.last n)*spin τ (Fin.last n)-overlap (restrictLeft σ) (restrictLeft τ))/(n+1) := by
    field_simp; ring
  rw [he,abs_div,abs_of_pos (show (0:ℝ)<n+1 by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := abs_sub (spin σ (Fin.last n)*spin τ (Fin.last n)) (overlap (restrictLeft σ) (restrictLeft τ))
  rw [abs_mul,spin_abs,spin_abs,one_mul] at h
  linarith [abs_overlap_le_one (restrictLeft σ) (restrictLeft τ)]

 

def mixedCavityCoeff (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ : Configuration (n+1)) : (Edge n ⊕ Fin n) ⊕ (Σ k : K, Fin (d k) → Fin n) → ℝ :=
  Sum.elim (fun u => β*cavityCoeff n σ u)
    (fun u => x u.1*pSpinCoeff n (d u.1) (restrictLeft σ) u.2)

omit [DecidableEq K] in
lemma mixedCavityCoeff_kernel {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration (n+1)) :
    kernel (mixedCavityCoeff n d β x) σ τ =
      kernel (fun s e => β*skCoeff (n+1) s e) σ τ+
      ∑ k,(x k)^2*(overlap (restrictLeft σ) (restrictLeft τ))^(d k) := by
  change (∑ u,mixedCavityCoeff n d β x σ u*mixedCavityCoeff n d β x τ u)=_
  rw [Fintype.sum_sum_type]
  simp only [mixedCavityCoeff,Sum.elim_inl,Sum.elim_inr,Fintype.sum_sigma]
  change kernel (fun s u => β*cavityCoeff n s u) σ τ+
    (∑ k,kernel (fun s u => x k*pSpinCoeff n (d k) s u) (restrictLeft σ) (restrictLeft τ))=_
  simp_rw [kernel_scale,pSpinCoeff_kernel hn]
  rw [cavityCoeff_kernel hn]

omit [DecidableEq K] in
lemma mixedCoeff_kernel_add {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration n) :
    kernel (mixedCoeff n d β x) σ τ = kernel (fun s e => β*skCoeff n s e) σ τ+
      ∑ k,(x k)^2*(overlap σ τ)^(d k) := by
  rw [mixedCoeff_kernel hn,kernel_scale,kernel,coeff_covariance hn]
  ring

omit [DecidableEq K] in
lemma mixedCavity_kernel_error {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration (n+1)) :
    |kernel (mixedCavityCoeff n d β x) σ τ-kernel (mixedCoeff (n+1) d β x) σ τ|≤
      (2/((n:ℝ)+1))*∑ k,(x k)^2*(d k:ℝ) := by
  rw [mixedCavityCoeff_kernel hn,mixedCoeff_kernel_add (Nat.succ_pos n)]
  rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
  have hp := pow_sub_lipschitz_unit (abs_overlap_le_one (restrictLeft σ) (restrictLeft τ))
    (abs_overlap_le_one σ τ) (d k)
  rw [abs_sub_comm (overlap (restrictLeft σ) (restrictLeft τ))] at hp
  have h := mul_le_mul_of_nonneg_left (overlap_restrict_difference hn σ τ) (Nat.cast_nonneg (d k))
  have h' := mul_le_mul_of_nonneg_left (hp.trans h) (sq_nonneg (x k))
  nlinarith only [h']

omit [DecidableEq K] in
lemma mixedCavity_diag {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ : Configuration (n+1)) :
    kernel (mixedCavityCoeff n d β x) σ σ=kernel (mixedCoeff (n+1) d β x) σ σ := by
  rw [mixedCavityCoeff_kernel hn,mixedCoeff_kernel_add (Nat.succ_pos n),overlap_self hn,overlap_self (Nat.succ_pos n)]

 

omit [DecidableEq K] in
theorem mixedCavity_pressure_error {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    |expected (mixedCavityCoeff n d β x)-expected (mixedCoeff (n+1) d β x)|≤
      Real.pi/((n:ℝ)+1)*(∑ k,(x k)^2*(d k:ℝ)) := by
  let M := (4/((n:ℝ)+1))*∑ k,(x k)^2*(d k:ℝ)
  have hM : 0≤M := by dsimp [M]; positivity
  have hi (σ τ : Configuration (n+1)) :
      |ParisiInterpolation.increment (mixedCavityCoeff n d β x) σ τ-
        ParisiInterpolation.increment (mixedCoeff (n+1) d β x) σ τ|≤M := by
    rw [increment_eq_kernel,increment_eq_kernel,mixedCavity_diag hn,mixedCavity_diag hn]
    have he : kernel (mixedCoeff (n+1) d β x) σ σ+kernel (mixedCoeff (n+1) d β x) τ τ-
        2*kernel (mixedCavityCoeff n d β x) σ τ-
        (kernel (mixedCoeff (n+1) d β x) σ σ+kernel (mixedCoeff (n+1) d β x) τ τ-
        2*kernel (mixedCoeff (n+1) d β x) σ τ)=
        -2*(kernel (mixedCavityCoeff n d β x) σ τ-kernel (mixedCoeff (n+1) d β x) σ τ) := by ring
    rw [he,abs_mul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have h := mul_le_mul_of_nonneg_left (mixedCavity_kernel_error hn d β x σ τ) (by norm_num : (0:ℝ)≤2)
    exact h.trans_eq (by dsimp [M]; ring)
  have h := expected_difference_le (mixedCoeff (n+1) d β x) (mixedCavityCoeff n d β x) hM hi
  convert h using 1
  dsimp [M]
  ring

 

def mixedIncrement (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) : ℝ :=
  expected (mixedCavityCoeff n d β x)-expected (mixedCoeff n d β x)

omit [DecidableEq K] in
lemma mixedIncrement_difference {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    |mixedIncrement n d β x-(expected (mixedCoeff (n+1) d β x)-expected (mixedCoeff n d β x))|≤
      Real.pi/((n:ℝ)+1)*(∑ k,(x k)^2*(d k:ℝ)) := by
  simpa only [mixedIncrement,sub_sub_sub_cancel_right] using mixedCavity_pressure_error hn d β x

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

variable {ι κ κ' : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype κ']

def independentCoeff (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (s : ι) : κ ⊕ κ' → ℝ := Sum.elim (A s) (B s)

omit [Fintype ι] [Nonempty ι] in
lemma kernel_independent (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (s t : ι) :
    kernel (independentCoeff A B) s t=kernel A s t+kernel B s t := by
  simp [kernel,independentCoeff,Fintype.sum_sum_type]

omit [Fintype ι] [Nonempty ι] in
lemma increment_independent (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (s t : ι) :
    ParisiInterpolation.increment (independentCoeff A B) s t=
      ParisiInterpolation.increment A s t+ParisiInterpolation.increment B s t := by
  simp only [increment_eq_kernel,kernel_independent]
  ring

lemma expected_independent_mono (A : ι → κ → ℝ) (B : ι → κ' → ℝ) :
    expected A≤expected (independentCoeff A B) := by
  apply expected_field_logPartition_le
  intro s t
  change ParisiInterpolation.increment A s t≤ParisiInterpolation.increment (independentCoeff A B) s t
  rw [increment_independent]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma expected_independent_error (A : ι → κ → ℝ) (B : ι → κ' → ℝ) {M : ℝ}
    (hM : 0≤M) (h : ∀ s t, ParisiInterpolation.increment B s t≤M) :
    expected (independentCoeff A B)-expected A≤M*Real.pi/4 := by
  have he := expected_difference_le A (independentCoeff A B) hM (fun s t => by
    rw [increment_independent,add_sub_cancel_left,abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact h s t)
  exact (le_abs_self _).trans he

lemma average_const (x : ι → ℝ) (c : ℝ) : average x (fun _ => c)=c := by
  simp [average,← Finset.sum_mul,sum_weight]

lemma logPartition_restrictLeft {n : ℕ} (x : Configuration n → ℝ) :
    logPartition (fun σ : Configuration (n+1) => x (restrictLeft σ))=logPartition x+Real.log 2 := by
  have h := logPartition_extend x (fun _ => 0)
  have he : SKCavity.extend x (fun _ => 0) = (fun σ : Configuration (n+1) => x (restrictLeft σ)) := by
    funext σ
    simp only [SKCavity.extend,mul_zero,add_zero]
  rw [he] at h
  simpa only [Real.cosh_zero,mul_one,average_const] using h

def liftOld {n : ℕ} (A : Configuration n → κ → ℝ) (σ : Configuration (n+1)) : κ → ℝ := A (restrictLeft σ)

lemma expected_liftOld {n : ℕ} (A : Configuration n → κ → ℝ) :
    expected (liftOld A)=expected A+Real.log 2 := by
  have hf (z : κ → ℝ) : field (liftOld A) z=fun σ => field A z (restrictLeft σ) := rfl
  unfold expected
  simp_rw [hf,logPartition_restrictLeft]
  rw [integral_add (integrable_logPartition (fun σ => integrable_field A σ)) (integrable_const _)]
  simp

 

omit [Fintype ι] [Nonempty ι] in
lemma increment_le_four_diagonal (B : ι → κ' → ℝ) (s₀ : ι)
    (hB : ∀ s k, |B s k|=|B s₀ k|) (s t : ι) :
    ParisiInterpolation.increment B s t≤4*kernel B s₀ s₀ := by
  unfold ParisiInterpolation.increment kernel
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hs := congrArg (fun x : ℝ => x^2) (hB s k)
  have ht := congrArg (fun x : ℝ => x^2) (hB t k)
  simp only [sq_abs] at hs ht
  nlinarith [sq_nonneg (B s k+B t k)]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

def siteCoeff (n : ℕ) (β : ℝ) (σ : Configuration (n+1)) (i : Fin n) : ℝ :=
  β*cavityScale n*spin σ (Fin.last n)*spin (restrictLeft σ) i

omit [DecidableEq K] in
lemma mixedCavity_split (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    expected (mixedCavityCoeff n d β x)=
      expected (independentCoeff (liftOld (mixedCoeff n d (β*coreScale n) x)) (siteCoeff n β)) := by
  apply expected_logPartition_eq_of_kernel
  intro σ τ
  simp only [kernel,mixedCavityCoeff,mixedCoeff,liftOld,siteCoeff,
    cavityCoeff,independentCoeff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_sigma]
  ac_rfl

omit [DecidableEq K] in
lemma mixed_core_correction (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    expected (mixedCoeff n d β x)=expected (independentCoeff
      (mixedCoeff n d (β*coreScale n) x) (fun σ e => β*cavityScale n*skCoeff n σ e)) := by
  apply expected_logPartition_eq_of_kernel
  intro σ τ
  have hc := scales_sum n
  simp only [kernel,independentCoeff,mixedCoeff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have hs : (∑ e, β*skCoeff n σ e*(β*skCoeff n τ e))=
      (∑ e, (β*coreScale n)*skCoeff n σ e*((β*coreScale n)*skCoeff n τ e))+
      (∑ e, β*cavityScale n*skCoeff n σ e*(β*cavityScale n*skCoeff n τ e)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    nlinarith only [congrArg (fun a : ℝ => a*(β^2*skCoeff n σ e*skCoeff n τ e)) hc]
  linarith only [hs]

lemma skCoeff_abs (n : ℕ) (σ τ : Configuration n) (e : Edge n) :
    |skCoeff n σ e|=|skCoeff n τ e| := by
  simp [skCoeff,abs_mul,spin_abs]

lemma correction_diagonal_le {n : ℕ} (hn : 0 < n) (β : ℝ) (σ : Configuration n) :
    kernel (fun σ e => β*cavityScale n*skCoeff n σ e) σ σ ≤ β^2/2 := by
  rw [kernel_scale,kernel,coeff_covariance hn,overlapSum_self]
  rw [mul_pow,cavityScale_sq]
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he : (β^2*(1/((n:ℝ)+1)))*(((n:ℝ)^2-n)/(2*n))=
      β^2*((n:ℝ)-1)/(2*(n+1)) := by field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*((n:ℝ)+1))).mpr
  nlinarith [sq_nonneg β]

omit [DecidableEq K] in
lemma core_pressure_lower {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    expected (mixedCoeff n d β x)-expected (mixedCoeff n d (β*coreScale n) x) ≤ Real.pi*β^2/2 := by
  rw [mixed_core_correction]
  have h := expected_independent_error (mixedCoeff n d (β*coreScale n) x)
      (fun σ e => β*cavityScale n*skCoeff n σ e) (M:=2*β^2) (by positivity) (fun s t => by
    have hh := increment_le_four_diagonal (fun σ e => β*cavityScale n*skCoeff n σ e) s
      (fun σ e => by simp only [abs_mul,skCoeff_abs n σ s e]) s t
    exact hh.trans (by nlinarith [correction_diagonal_le hn β s]))
  exact h.trans_eq (by ring)

 
omit [DecidableEq K] in
theorem mixedIncrement_lower {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    Real.log 2-Real.pi*β^2/2 ≤  mixedIncrement n d β x := by
  have hlo := expected_independent_mono (liftOld (mixedCoeff n d (β*coreScale n) x)) (siteCoeff n β)
  rw [← mixedCavity_split,expected_liftOld] at hlo
  have hup := core_pressure_lower hn d β x
  unfold mixedIncrement
  linarith

lemma siteCoeff_abs (n : ℕ) (β : ℝ) (σ τ : Configuration (n+1)) (i : Fin n) :
    |siteCoeff n β σ i|=|siteCoeff n β τ i| := by
  simp only [siteCoeff,abs_mul,spin_abs,mul_one]

lemma siteCoeff_diag_le (n : ℕ) (β : ℝ) (σ : Configuration (n+1)) :
    kernel (siteCoeff n β) σ σ ≤ β^2 := by
  have he (i : Fin n) : siteCoeff n β σ i*siteCoeff n β σ i=β^2*cavityScale n^2 := by
    dsimp [siteCoeff]
    nlinarith only [spin_sq σ (Fin.last n),spin_sq (restrictLeft σ) i,
      congrArg (fun a : ℝ => β^2*cavityScale n^2*a) (spin_sq σ (Fin.last n)),
      congrArg (fun a : ℝ => β^2*cavityScale n^2*spin σ (Fin.last n)^2*a) (spin_sq (restrictLeft σ) i)]
  simp only [kernel,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,cavityScale_sq]
  have hpos : (0:ℝ)<n+1 := by positivity
  have he' : (n:ℝ)*(β^2*(1/(n+1)))=β^2*n/(n+1) := by ring
  rw [he']
  exact (div_le_iff₀ hpos).mpr (by nlinarith [sq_nonneg β])

 
omit [DecidableEq K] in
theorem mixedIncrement_upper (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    mixedIncrement n d β x ≤ Real.log 2+Real.pi*β^2 := by
  have hlo := expected_independent_mono (mixedCoeff n d (β*coreScale n) x)
    (fun σ e => β*cavityScale n*skCoeff n σ e)
  rw [← mixed_core_correction] at hlo
  have hup := expected_independent_error (liftOld (mixedCoeff n d (β*coreScale n) x))
    (siteCoeff n β) (M:=4*β^2) (by positivity) (fun s t =>
      (increment_le_four_diagonal (siteCoeff n β) s (fun σ i => siteCoeff_abs n β σ s i) s t).trans
        (by nlinarith [siteCoeff_diag_le n β s]))
  rw [← mixedCavity_split,expected_liftOld] at hup
  unfold mixedIncrement
  nlinarith only [hlo,hup]

omit [DecidableEq K] in
lemma mixedIncrement_bounded {n : ℕ} (hn : 0 < n) (d : K → ℕ) (β : ℝ) :
    ∃ M : ℝ, ∀ x, |mixedIncrement n d β x| ≤ M := by
  refine ⟨|Real.log 2|+Real.pi*β^2,fun x => abs_le.mpr ⟨?_,?_⟩⟩
  · have h := mixedIncrement_lower hn d β x
    nlinarith [neg_abs_le (Real.log 2),Real.pi_pos,sq_nonneg β]
  · exact (mixedIncrement_upper n d β x).trans (add_le_add (le_abs_self _) le_rfl)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

lemma continuous_expected_coeff : Continuous (fun A : ι → κ → ℝ => expected A) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro A₀
  let H (A : ι → κ → ℝ) := ∑ s, ∑ t, |ParisiInterpolation.increment A s t-ParisiInterpolation.increment A₀ s t|
  have hc : Continuous H := by unfold H ParisiInterpolation.increment; fun_prop
  have hH : H A₀=0 := by simp [H]
  have hB (A : ι → κ → ℝ) : |expected A-expected A₀| ≤ H A*Real.pi/4 := by
    apply expected_difference_le A₀ A (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    intro s t
    have h1 : |ParisiInterpolation.increment A s t-ParisiInterpolation.increment A₀ s t| ≤ 
        ∑ j : ι, |ParisiInterpolation.increment A s j-ParisiInterpolation.increment A₀ s j| :=
      Finset.single_le_sum (f := fun j : ι => |ParisiInterpolation.increment A s j-ParisiInterpolation.increment A₀ s j|) (fun j _ => abs_nonneg _) (Finset.mem_univ t)
    have h2 : (∑ j : ι, |ParisiInterpolation.increment A s j-ParisiInterpolation.increment A₀ s j|) ≤ H A :=
      Finset.single_le_sum (f := fun j : ι => ∑ t : ι, |ParisiInterpolation.increment A j t-ParisiInterpolation.increment A₀ j t|) (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    exact h1.trans h2
  have ht : Tendsto (fun A => |expected A-expected A₀|) (𝓝 A₀) (𝓝 0) := by
    have hh := ((hc.continuousAt (x := A₀)).mul_const Real.pi).div_const 4
    change Tendsto (fun A => H A*Real.pi/4) (𝓝 A₀) (𝓝 (H A₀*Real.pi/4)) at hh
    rw [hH,zero_mul,zero_div] at hh
    exact squeeze_zero (fun _ => abs_nonneg _) hB hh
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using ht

lemma continuous_mixedIncrement (n : ℕ) {K : Type*} [Fintype K]
    (d : K → ℕ) (β : ℝ) : Continuous (mixedIncrement n d β) := by
  classical
  unfold mixedIncrement
  apply Continuous.sub
  · apply continuous_expected_coeff.comp
    apply continuous_pi
    intro σ
    apply continuous_pi
    intro u
    cases u <;> simp only [mixedCavityCoeff,Sum.elim_inl,Sum.elim_inr] <;> fun_prop
  · exact continuous_expected_coeff.comp (continuous_mixedCoeff n d β)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

lemma sum_fin_increment (a : ℕ → ℝ) (N M : ℕ) :
    (∑ i : Fin M, (a (N+i+1)-a (N+i)))=a (N+M)-a N := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    simp only [Nat.add_assoc]
    ring

lemma expected_sk_pressure (n : ℕ) (β : ℝ) :
    expected (fun σ e => β*skCoeff n σ e)=pressure β n := by
  unfold expected
  simp only [field_scale,field_skCoeff]
  rfl

 

omit [DecidableEq K] in
theorem sum_mixedIncrement_window {N : ℕ} (hN : 0 < N) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    (∑ i : Fin N, mixedIncrement (N+i) d β x) ≤ pressure β (N+N)-pressure β N+
      Real.pi*(2*(∑ k,(x k)^2)+(∑ k,(x k)^2*(d k:ℝ))) := by
  let S := ∑ k,(x k)^2
  let D := ∑ k,(x k)^2*(d k:ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hN' : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hstep (i : Fin N) : mixedIncrement (N+i) d β x ≤ 
      expected (mixedCoeff (N+i+1) d β x)-expected (mixedCoeff (N+i) d β x)+Real.pi/(N:ℝ)*D := by
    have hi : 0<N+i.val := by omega
    have h := (le_abs_self _).trans (mixedIncrement_difference hi d β x)
    have hden : (N:ℝ) ≤ (N+i.val:ℕ)+1 := by push_cast; linarith [show (0:ℝ) ≤ (i.val:ℝ) from Nat.cast_nonneg _]
    have hd := div_le_div_of_nonneg_left Real.pi_pos.le hN' hden
    have hm := mul_le_mul_of_nonneg_right hd hD
    dsimp [D] at hm
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hstep i)
  rw [Finset.sum_add_distrib,sum_fin_increment (fun q => expected (mixedCoeff q d β x)) N N] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have he : (N:ℝ)*(Real.pi/(N:ℝ)*D)=Real.pi*D := by field_simp
  rw [he] at hs
  have h0 := mixed_pressure_error hN d β x
  have h1 := mixed_pressure_error (show 0<N+N by omega) d β x
  rw [expected_sk_pressure] at h0 h1
  have hl := (abs_le.mp h0).1
  have hu := (abs_le.mp h1).2
  dsimp [S,D] at *
  linarith

lemma sum_mixedIncrement_box {N m : ℕ} (hN : 0 < N) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s : ℝ} (hs : 0<s) (x : Fin (m+1) → ℝ) (hx : ∀ k, x k∈Set.Icc s (2*s)) :
    (∑ i : Fin N, mixedIncrement (N+i) d β x) ≤ pressure β (N+N)-pressure β N+
      Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ)))*s^2 := by
  have hb (k) : (x k)^2 ≤ 4*s^2 := by nlinarith [(hx k).1,(hx k).2]
  have hsum := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hb k)
  have hsum' := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) =>
    mul_le_mul_of_nonneg_right (hb k) (Nat.cast_nonneg (d k)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum'
  have h := sum_mixedIncrement_window hN d β x
  have hh : 2*(∑ k,(x k)^2)+(∑ k,(x k)^2*(d k:ℝ)) ≤ 
      (8*(m+1:ℕ)+4*(∑ k,(d k:ℝ)))*s^2 := by nlinarith only [hsum,hsum']
  have hp := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
  nlinarith only [h,hp]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma integrable_box_of_bounded {m : ℕ} {a b : ℝ} {F : (Fin m → ℝ) → ℝ}
    (hc : Continuous F) (hb : ∃ M : ℝ, ∀ x, |F x| ≤ M) : Integrable F (boxLaw m a b) := by
  obtain ⟨M,hM⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable M (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hM x)

lemma integral_box_mixedError_le {m n : ℕ} (hn : 0 < n) (d : Fin (m+1) → ℕ) (β V : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) (k : Fin (m+1)) :
    (∫ x, mixedError n d β δ V k x ∂boxLaw (m+1) s (2*s)) ≤ 5+4*V/δ+12*δ := by
  have hab : s<2*s := by linarith
  let := intervalLaw_probability hab
  have hI := integrable_box_of_bounded (a:=s) (b:=2*s) (continuous_mixedError n d β δ V k) (mixedError_bounded n d β δ V k)
  rw [integral_boxLaw_coordinate hab k hI]
  have hi : Integrable (fun y : Fin m → ℝ => ∫ t, mixedError n d β δ V k (k.insertNth t y)
      ∂intervalLaw s (2*s)) (boxLaw m s (2*s)) := by
    let T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) k).symm
    have hm : MeasurePreserving T ((intervalLaw s (2*s)).prod (boxLaw m s (2*s))) (boxLaw (m+1) s (2*s)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => intervalLaw s (2*s)) k).symm
    exact ((hm.integrable_comp (continuous_mixedError n d β δ V k).aestronglyMeasurable).mpr hI).integral_prod_right
  have he := integral_mono hi (integrable_const (5+4*V/δ+12*δ)) (fun y => by
    rw [integral_intervalLaw hab.le]
    have h := integral_mixedError_le hn d β V hs hδ hδs k y
    have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
    rw [show 2*s-s=s by ring]
    exact hh.trans_eq (by field_simp))
  simpa using he

 

lemma exists_box_index_le_integrable {N m : ℕ} (hN : 0 < N) {a b B : ℝ} (hab : a<b)
    (F : Fin N → (Fin m → ℝ) → ℝ) (hint : ∀ i, Integrable (F i) (boxLaw m a b))
    (hi : (∫ x, ∑ i, F i x ∂boxLaw m a b) ≤ (N:ℝ)*B) :
    ∃ (i : Fin N) (x : Fin m → ℝ), (∀ k, x k∈Set.Icc a b) ∧ F i x ≤ B := by
  let := intervalLaw_probability hab
  have hI : Integrable (fun x => ∑ i, F i x) (boxLaw m a b) :=
    integrable_finsetSum _ fun i _ => hint i
  have hnull : boxLaw m a b {x | ¬∀ k, x k∈Set.Icc a b}=0 := ae_iff.mp (boxLaw_ae m a b)
  obtain ⟨x,hx,hxle⟩ := exists_notMem_null_le_integral hI hnull
  have hs := hxle.trans hi
  have he : ∃ i, F i x ≤ B := by
    by_contra! h
    have hh := Finset.sum_lt_sum_of_nonempty (show (Finset.univ : Finset (Fin N)).Nonempty from
      ⟨⟨0,hN⟩,Finset.mem_univ _⟩) (fun i (_ : i∈Finset.univ) => h i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    linarith
  obtain ⟨i,hi⟩ := he
  exact ⟨i,x,not_not.mp hx,hi⟩

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def coreFluctuationBound (n m : ℕ) (β s : ℝ) : ℝ :=
  Real.sqrt ((β*coreScale n)^2*n/2+9*(m+1:ℕ)*s^2)

def coreError {m : ℕ} (n : ℕ) (d : Fin (m+1) → ℕ) (β s δ : ℝ) (x : Fin (m+1) → ℝ) : ℝ :=
  ∑ k, mixedError n d (β*coreScale n) δ (coreFluctuationBound n m β s) k x

lemma coreError_integrable {m : ℕ} (n : ℕ) (d : Fin (m+1) → ℕ) (β s δ a b : ℝ) :
    Integrable (coreError n d β s δ) (boxLaw (m+1) a b) :=
  integrable_finsetSum _ fun k _ => integrable_box_of_bounded
    (continuous_mixedError n d (β*coreScale n) δ _ k) (mixedError_bounded n d (β*coreScale n) δ _ k)

lemma coreError_dominates {m n : ℕ} (hn : 0 < n) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) (x : Fin (m+1) → ℝ)
    (hx : ∀ k, x k∈Set.Icc s (2*s)) (k : Fin (m+1)) :
    energyDeviation (mixedCoeff n d (β*coreScale n) x) (mixedNoise n d k)
      (energyMean (mixedCoeff n d (β*coreScale n) x) (mixedNoise n d k)) ≤ coreError n d β s δ x := by
  have hdom (j) := mixedError_dominates hn d (β*coreScale n) hs hδ hδs j x hx
  simp only [Fintype.card_fin] at hdom
  apply (hdom k).trans
  exact Finset.single_le_sum (fun j _ => (energyDeviation_nonneg _ _ _).trans (hdom j)) (Finset.mem_univ k)

lemma coreError_nonneg {m n : ℕ} (hn : 0 < n) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) (x : Fin (m+1) → ℝ)
    (hx : ∀ k, x k∈Set.Icc s (2*s)) : 0 ≤ coreError n d β s δ x :=
  (energyDeviation_nonneg _ _ _).trans (coreError_dominates hn d β hs hδ hδs x hx 0)

lemma integral_coreError_le {m n : ℕ} (hn : 0 < n) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ U : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s)
    (hU : coreFluctuationBound n m β s ≤ U) :
    (∫ x, coreError n d β s δ x ∂boxLaw (m+1) s (2*s)) ≤
      (m+1:ℕ)*(5+4*U/δ+12*δ) := by
  unfold coreError
  rw [integral_finsetSum _ (fun k _ => integrable_box_of_bounded
    (continuous_mixedError n d (β*coreScale n) δ _ k) (mixedError_bounded n d (β*coreScale n) δ _ k))]
  have h := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) =>
    integral_box_mixedError_le hn d (β*coreScale n) (coreFluctuationBound n m β s) hs hδ hδs k)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ) ≤ 4)) hδ.le
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (m+1))
  linarith

def cavityWindowBudget {m : ℕ} (N : ℕ) (d : Fin (m+1) → ℕ) (β s δ ell U : ℝ) : ℝ :=
  (pressure β (N+N)-pressure β N+Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ)))*s^2)/(N:ℝ)+
    (ell/s)*(m+1:ℕ)*(5+4*U/δ+12*δ)

 

theorem exists_cavity_GG_choice {N m : ℕ} (hN : 0 < N) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ ell U : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) (hell : 0<ell)
    (hU : ∀ i : Fin N, coreFluctuationBound (N+i) m β s ≤ U) :
    ∃ (j : Fin N) (x : Fin (m+1) → ℝ), (∀ k, x k∈Set.Icc s (2*s)) ∧
      mixedIncrement (N+j) d β x ≤ cavityWindowBudget N d β s δ ell U ∧
      ∀ (k : Fin (m+1)) (r : ℕ) (i : Fin r) (f : (Fin r → Configuration (N+j)) → ℝ),
      (∀ σ, |f σ| ≤ 1) → |mixedGGDefect d (β*coreScale (N+j)) x k i f| ≤
        (cavityWindowBudget N d β s δ ell U-(Real.log 2-Real.pi*β^2/2))/ell := by
  let μ := boxLaw (m+1) s (2*s)
  have hab : s<2*s := by linarith
  let := intervalLaw_probability hab
  let A (j : Fin N) := mixedIncrement (N+j) d β
  let E (j : Fin N) := coreError (N+j) d β s δ
  let F (j : Fin N) (x : Fin (m+1) → ℝ) := A j x+(ell/s)*E j x
  have hn (j : Fin N) : 0<N+j.val := by omega
  have hIA (j : Fin N) : Integrable (A j) μ :=
    integrable_box_of_bounded (continuous_mixedIncrement _ d β) (mixedIncrement_bounded (hn j) d β)
  have hIE (j : Fin N) : Integrable (E j) μ := coreError_integrable _ d β s δ s (2*s)
  have hIF (j : Fin N) : Integrable (F j) μ := (hIA j).add ((hIE j).const_mul _)
  let C := pressure β (N+N)-pressure β N+Real.pi*(8*(m+1:ℕ)+4*(∑ k,(d k:ℝ)))*s^2
  have hIAall : Integrable (fun x => ∑ j, A j x) μ := integrable_finsetSum _ fun j _ => hIA j
  have hIEall : Integrable (fun x => ∑ j, E j x) μ := integrable_finsetSum _ fun j _ => hIE j
  have hA : (∫ x, ∑ j, A j x ∂μ) ≤ C := by
    have hh := integral_mono_ae hIAall (integrable_const C) ((boxLaw_ae (m+1) s (2*s)).mono (fun x hx =>
      sum_mixedIncrement_box hN d β hs x hx))
    simpa [μ] using hh
  have hE : (∫ x, ∑ j, E j x ∂μ) ≤ (N:ℝ)*((m+1:ℕ)*(5+4*U/δ+12*δ)) := by
    rw [integral_finsetSum _ (fun j _ => hIE j)]
    have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => integral_coreError_le (hn j) d β hs hδ hδs (hU j))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hF : (∫ x, ∑ j, F j x ∂μ) ≤ (N:ℝ)*cavityWindowBudget N d β s δ ell U := by
    simp only [F,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [integral_add hIAall (hIEall.const_mul _),integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hE (div_nonneg hell.le hs.le)
    have he : (N:ℝ)*cavityWindowBudget N d β s δ ell U=
        C+(ell/s)*((N:ℝ)*((m+1:ℕ)*(5+4*U/δ+12*δ))) := by
      dsimp [cavityWindowBudget,C]
      field_simp
    rw [he]
    linarith
  obtain ⟨j,x,hx,hcost⟩ := exists_box_index_le_integrable hN hab F hIF hF
  have hnon := coreError_nonneg (hn j) d β hs hδ hδs x hx
  have hlo := mixedIncrement_lower (hn j) d β x
  change mixedIncrement (N+j) d β x+(ell/s)*coreError (N+j) d β s δ x ≤ _ at hcost
  refine ⟨j,x,hx,?_,fun k r i f hf => ?_⟩
  · nlinarith only [hcost,mul_nonneg (div_nonneg hell.le hs.le) hnon]
  · have hgg := mixedGGDefect_bound (hn j) d (β*coreScale (N+j)) x k i f (by norm_num : (0:ℝ) ≤ 1) hf
    rw [one_mul,abs_mul,abs_of_nonneg (hs.le.trans (hx k).1)] at hgg
    have hd := coreError_dominates (hn j) d β hs hδ hδs x hx k
    have hmul := mul_le_mul_of_nonneg_right (hx k).1 (abs_nonneg (mixedGGDefect d (β*coreScale (N+j)) x k i f))
    have hEs : |mixedGGDefect d (β*coreScale (N+j)) x k i f| ≤ coreError (N+j) d β s δ x/s := by
      apply (le_div_iff₀ hs).mpr
      nlinarith only [hgg,hd,hmul]
    apply hEs.trans
    apply (le_div_iff₀ hell).mpr
    have he : coreError (N+j) d β s δ x/s*ell=(ell/s)*coreError (N+j) d β s δ x := by ring
    rw [he]
    linarith

end SKCavity

end

end OAI
