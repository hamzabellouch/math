import Mathlib
import OAI.Probability.ParisiFinite.TreeNodeDepth

namespace OAI

/-! Log Series Term Bound. -/

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
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma log_series_term_bound {x z : ℝ} (hx : 0≤x ∧ x≤1) (hz : |z|<1) (n : ℕ) :
    ‖-(z*x)^(n+1)/(n+1:ℕ)‖≤|z|^n := by
  have hn : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_pow,abs_mul,abs_of_nonneg hx.1,
    abs_of_nonneg (by positivity : (0:ℝ)≤(n+1:ℕ))]
  calc
    (|z| * x)^(n+1)/(n+1:ℕ) ≤ |z|^(n+1)/(n+1:ℕ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hx.1)
        (mul_le_of_le_one_right (abs_nonneg _) hx.2) _) (by positivity)
    _ ≤ |z|^(n+1) := div_le_self (pow_nonneg (abs_nonneg _) _) hn
    _ ≤ |z|^n := by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _) hz.le

lemma integral_log_unit_series {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} (hY : Measurable Y) (hb : ∀ sample,0≤Y sample ∧ Y sample≤1) {z : ℝ} (hz : |z|<1) :
    (∫ sample,Real.log (1-z*Y sample) ∂ν)=
      ∑' n,-(∫ sample,Y sample^(n+1) ∂ν)*z^(n+1)/(n+1:ℕ) := by
  let F (n : ℕ) (sample : Ω) : ℝ := -(z*Y sample)^(n+1)/(n+1:ℕ)
  have hFi (n : ℕ) : Integrable (F n) ν :=
    integrable_of_uniform_abs (by fun_prop) (fun sample => by
      simpa only [Real.norm_eq_abs] using log_series_term_bound (hb sample) hz n)
  have hs : Summable (fun n => ∫ sample,‖F n sample‖ ∂ν) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun sample => norm_nonneg _))
      (fun n => ?_) (summable_geometric_of_lt_one (abs_nonneg z) hz)
    simpa using integral_mono (hFi n).norm (integrable_const (|z|^n))
      (fun sample => log_series_term_bound (hb sample) hz n)
  have hseries : ∀ sample,HasSum (fun n => F n sample) (Real.log (1-z*Y sample)) := by
    intro sample
    have hzx : |z*Y sample|<1 := ((by
      rw [abs_mul,abs_of_nonneg (hb sample).1]
      exact mul_le_of_le_one_right (abs_nonneg z) (hb sample).2) : |z*Y sample|≤|z|).trans_lt hz
    simpa only [F,Nat.cast_add,Nat.cast_one,neg_div,neg_neg] using (Real.hasSum_pow_div_log_of_abs_lt_one hzx).neg
  have hi := hasSum_integral_of_summable_integral_norm hFi hs
  simp_rw [(hseries _).tsum_eq] at hi
  rw [← hi.tsum_eq]
  apply tsum_congr
  intro n
  simp only [F,mul_pow,neg_div,integral_neg,integral_div,integral_const_mul]
  ring

 

theorem empirical_log_limit_of_distinct_moments
    {Ω : ℕ → Type*} [∀ r,MeasurableSpace (Ω r)] (ν : (r : ℕ) → Measure (Ω r))
    [∀ r,IsProbabilityMeasure (ν r)] (X : (r : ℕ) → Ω r → Fin (r+1) → ℝ)
    (hX : ∀ r i,Measurable (fun sample => X r sample i))
    (hb : ∀ r sample i,0≤X r sample i ∧ X r sample i≤1)
    (M : ℕ → ℝ) (hM : ∀ k,0≤M k ∧ M k≤1)
    (he : ∀ r k (e : Fin k → Fin (r+1)),Function.Injective e →
      (∫ sample,∏ i,X r sample (e i) ∂ν r)=M k)
    {z : ℝ} (hz : |z|<1) :
    Tendsto (fun r => ∫ sample,Real.log (1-z*((∑ i,X r sample i)/(r+1:ℕ))) ∂ν r) atTop
      (𝓝 (∑' n,-M (n+1)*z^(n+1)/(n+1:ℕ))) := by
  let Y (r : ℕ) (sample : Ω r) : ℝ := (∑ i,X r sample i)/(r+1:ℕ)
  have hYm (r : ℕ) : Measurable (Y r) := (Finset.measurable_sum _ (fun i _ => hX r i)).div_const _
  have hYb (r : ℕ) (sample : Ω r) : 0≤Y r sample ∧ Y r sample≤1 := by
    dsimp only [Y]
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hb r sample i).1)) (by positivity)
    · apply (div_le_one (by positivity)).mpr
      simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (hb r sample i).2)
  have hprod (r k : ℕ) (e : Fin k → Fin (r+1)) (sample : Ω r) :
      0≤∏ i,X r sample (e i) ∧ (∏ i,X r sample (e i))≤1 :=
    ⟨Finset.prod_nonneg (fun i _ => (hb r sample (e i)).1),
       Finset.prod_le_one₀ (fun i _ => (hb r sample (e i)).1) (fun i _ => (hb r sample (e i)).2)⟩
  have hprodi (r k : ℕ) (e : Fin k → Fin (r+1)) :
      Integrable (fun sample => ∏ i,X r sample (e i)) (ν r) := by
    apply integrable_of_uniform_abs (Finset.measurable_prod _ (fun i _ => hX r (e i)))
    intro sample
    rw [abs_of_nonneg (hprod r k e sample).1]
    exact (hprod r k e sample).2
  have hmom (k : ℕ) : Tendsto (fun r => ∫ sample,Y r sample^k ∂ν r) atTop (𝓝 (M k)) := by
    have hh (r : ℕ) : (∫ sample,Y r sample^k ∂ν r)=
        (∑ e : Fin k → Fin (r+1),∫ sample,∏ i,X r sample (e i) ∂ν r)/(r+1:ℕ)^k := by
      simp only [Y,div_pow,Fintype.sum_pow,integral_div]
      rw [integral_finsetSum Finset.univ (fun e _ => hprodi r k e)]
    simp_rw [hh]
    apply replica_average_moment_tendsto k _ (hM k)
    · intro r e
      refine ⟨integral_nonneg (fun sample => (hprod r k e sample).1),?_⟩
      simpa using integral_mono (hprodi r k e) (integrable_const (1:ℝ)) (fun sample => (hprod r k e sample).2)
    · exact fun r e h => he r k e h
  have hlog (r : ℕ) := integral_log_unit_series (ν r) (hYm r) (hYb r) hz
  change Tendsto (fun r => ∫ sample,Real.log (1-z*Y r sample) ∂ν r) _ _
  simp_rw [hlog]
  apply tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one (abs_nonneg z) hz)
  · intro n
    exact (((hmom (n+1)).neg).mul_const (z^(n+1))).div_const _
  · apply Eventually.of_forall
    intro r n
    have hbb : 0≤(∫ sample,Y r sample^(n+1) ∂ν r) ∧ (∫ sample,Y r sample^(n+1) ∂ν r)≤1 := by
      refine ⟨integral_nonneg (fun sample => pow_nonneg (hYb r sample).1 _),?_⟩
      have hi : Integrable (fun sample => Y r sample^(n+1)) (ν r) := by
        apply integrable_of_uniform_abs ((hYm r).pow_const _)
        intro sample
        rw [abs_of_nonneg (pow_nonneg (hYb r sample).1 _)]
        exact pow_le_one₀ (hYb r sample).1 (hYb r sample).2
      simpa using integral_mono hi (integrable_const (1:ℝ))
        (fun sample => pow_le_one₀ (hYb r sample).1 (hYb r sample).2)
    have hh := normalized_moment_bound hbb z (n+1)
    have hzpow : |z|^(n+1)≤|z|^n := by
      rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _) hz.le
    convert hh.trans hzpow using 1
    congr 1
    push_cast
    ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def treePathVector {d r : ℕ} (T : PartitionTree d r) (z : TreeNode T → ℝ)
    (i : Fin r) (k : Fin d) : ℝ := z (treeNodePath T i k)

lemma treePathVector_continuous {d r : ℕ} (T : PartitionTree d r) :
    Continuous (treePathVector T) := by unfold treePathVector; fun_prop

def treePathLaw {d r : ℕ} (T : PartitionTree d r) : Measure (Fin r → Fin d → ℝ) :=
  (gaussianLaw (TreeNode T)).map (treePathVector T)

instance treePathLaw_probability {d r : ℕ} (T : PartitionTree d r) :
    IsProbabilityMeasure (treePathLaw T) := by
  unfold treePathLaw
  infer_instance

lemma integral_treePathLaw {d r : ℕ} (T : PartitionTree d r)
    (f : (Fin r → Fin d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ s,f s ∂treePathLaw T)=∫ z,f (treePathVector T z) ∂gaussianLaw (TreeNode T) :=
  integral_map (treePathVector_continuous T).measurable.aemeasurable hf.aestronglyMeasurable

def pathCoeff {d r : ℕ} (T : PartitionTree d r) (i : Fin r×Fin d) (n : TreeNode T) : ℝ :=
  if treeNodePath T i.1 i.2=n then 1 else 0

lemma field_pathCoeff {d r : ℕ} (T : PartitionTree d r) (z : TreeNode T → ℝ) (i : Fin r×Fin d) :
    field (pathCoeff T) z i=treePathVector T z i.1 i.2 := by
  classical
  simp [field,pathCoeff,treePathVector]

lemma kernel_pathCoeff {d r : ℕ} (T : PartitionTree d r) (i j : Fin r×Fin d) :
    kernel (pathCoeff T) i j=if treeNodePath T i.1 i.2=treeNodePath T j.1 j.2 then 1 else 0 := by
  classical
  unfold kernel pathCoeff
  rw [Finset.sum_eq_single (treeNodePath T i.1 i.2)]
  · simp [eq_comm]
  · intro n _ hn
    simp [Ne.symm hn]
  · simp

lemma treePath_marginal_integral {d r k : ℕ} (T : PartitionTree d r) (U : PartitionTree d k)
    (e : Fin k → Fin r)
    (he : ∀ (l : Fin d) (i j : Fin k),treeCodes T l.succ (e i)=treeCodes T l.succ (e j) ↔
      treeCodes U l.succ i=treeCodes U l.succ j)
    (f : (Fin k → Fin d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ s,f (fun i => s (e i)) ∂treePathLaw T)=(∫ s,f s ∂treePathLaw U) := by
  have hp (i j : Fin k×Fin d) :
      treeNodePath T (e i.1) i.2=treeNodePath T (e j.1) j.2 ↔
      treeNodePath U i.1 i.2=treeNodePath U j.1 j.2 := by
    constructor
    · intro h
      have hkl := treeNodePath_eq_levels T _ _ _ _ h
      obtain ⟨i,l⟩ := i
      obtain ⟨j,k⟩ := j
      dsimp only at hkl h ⊢
      subst k
      rw [treeNodePath_eq_iff] at h ⊢
      exact (he l i j).mp h
    · intro h
      have hkl := treeNodePath_eq_levels U _ _ _ _ h
      obtain ⟨i,l⟩ := i
      obtain ⟨j,k⟩ := j
      dsimp only at hkl h ⊢
      subst k
      rw [treeNodePath_eq_iff] at h ⊢
      exact (he l i j).mpr h
  have hk : kernel (fun i : Fin k×Fin d => pathCoeff T (e i.1,i.2))=kernel (pathCoeff U) := by
    funext i j
    change kernel (pathCoeff T) (e i.1,i.2) (e j.1,j.2)=_
    simp only [kernel_pathCoeff,hp]
  rw [integral_treePathLaw T (fun s => f (fun i => s (e i))) (hf.comp (by fun_prop)),integral_treePathLaw U f hf]
  have hh := integral_field_eq_of_kernel (fun i : Fin k×Fin d => pathCoeff T (e i.1,i.2))
    (pathCoeff U) hk (fun x => f (fun i l => x (i,l))) (hf.comp (by fun_prop))
  convert hh using 1
  · congr 1; funext z; congr 1; funext i l
    exact (field_pathCoeff T z (e i,l)).symm
  · congr 1; funext z; congr 1; funext i l
    exact (field_pathCoeff U z (i,l)).symm

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def hierarchySampleLaw {d : ℕ} (μ : ProbabilityMeasure OverlapArray) (q : Fin (d+1) → ℝ)
    (r : ℕ) : Measure (Fin r → Fin d → ℝ) :=
  ∑ T : PartitionTree d r,(μ:Measure OverlapArray) (hierarchyEvent (treeCodes T) q) • treePathLaw T

def hierarchyBlockSample {d r : ℕ} (q : Fin (d+1) → ℝ)
    (f : (Fin r → Fin d → ℝ) → ℝ) (A : OverlapBlock r) : ℝ :=
  ∑ T : PartitionTree d r,(hierarchyBlock (treeCodes T) q).indicator
    (fun _ => ∫ s,f s ∂treePathLaw T) A

lemma hierarchyBlockSample_measurable {d r : ℕ} (q : Fin (d+1) → ℝ)
    (f : (Fin r → Fin d → ℝ) → ℝ) : Measurable (hierarchyBlockSample q f) := by
  apply Finset.measurable_sum
  intro T _
  exact measurable_const.indicator (hierarchyBlock_measurable _ _)

lemma hierarchyBlockSample_on_event {d r : ℕ} (q : Fin (d+1) → ℝ)
    (f : (Fin r → Fin d → ℝ) → ℝ) (T : PartitionTree d r)
    {A : OverlapBlock r} (hA : A∈hierarchyBlock (treeCodes T) q) :
    hierarchyBlockSample q f A=∫ s,f s ∂treePathLaw T := by
  unfold hierarchyBlockSample
  rw [Finset.sum_eq_single T]
  · exact Set.indicator_of_mem hA _
  · intro U _ hUT
    apply Set.indicator_of_notMem
    intro hU
    apply hUT
    exact tree_eq_of_same_relations U T (fun k i j => (hU k i j).symm.trans (hA k i j))
  · simp

lemma hierarchySampleLaw_integral {d r : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {f : (Fin r → Fin d → ℝ) → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ s,|f s|≤C) :
    (∫ s,f s ∂hierarchySampleLaw μ q r)=
      ∑ T : PartitionTree d r,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q)*
        ∫ s,f s ∂treePathLaw T := by
  unfold hierarchySampleLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,smul_eq_mul,Measure.real]
  · intro T _
    exact (integrable_of_uniform_abs hf hb).smul_measure (measure_ne_top _ _)

lemma hierarchySampleLaw_integral_block {d r : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {f : (Fin r → Fin d → ℝ) → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ s,|f s|≤C) :
    (∫ s,f s ∂hierarchySampleLaw μ q r)=
      ∫ R,hierarchyBlockSample q f (blockOfArray r R) ∂(μ:Measure OverlapArray) := by
  rw [hierarchySampleLaw_integral μ q hf hb]
  have he (R : OverlapArray) : hierarchyBlockSample q f (blockOfArray r R)=
      ∑ T : PartitionTree d r,(hierarchyEvent (treeCodes T) q).indicator
        (fun _ => ∫ s,f s ∂treePathLaw T) R := rfl
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T _
    rw [integral_indicator_const _ (hierarchyEvent_measurable _ _)]
    rfl
  · intro T _
    exact (integrable_const _).indicator (hierarchyEvent_measurable _ _)

lemma hierarchySampleLaw_probability {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r : ℕ} (hr : 0<r) :
    IsProbabilityMeasure (hierarchySampleLaw μ q r) := by
  constructor
  unfold hierarchySampleLaw
  simp only [Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  have hc := hierarchy_partition_cover_all hG hgg hu q hq h0 h1 hr
  rw [measure_iUnion] at hc
  · simpa only [tsum_fintype] using hc
  · exact fun T U htu => tree_hierarchy_disjoint htu q
  · exact fun T => hierarchyEvent_measurable _ _

 

theorem hierarchySampleLaw_marginal_integral {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r k : ℕ} (hr : 0<r) (hk : 0<k)
    (e : Fin k → Fin r) (he : Function.Injective e)
    {f : (Fin k → Fin (d+1) → ℝ) → ℝ} {C : ℝ} (hf : Measurable f) (hb : ∀ s,|f s|≤C) :
    (∫ s,f (fun i => s (e i)) ∂hierarchySampleLaw μ q r)=
      ∫ s,f s ∂hierarchySampleLaw μ q k := by
  let B : Set (OverlapBlock k) := ⋃ U : PartitionTree (d+1) k,hierarchyBlock (treeCodes U) q
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun U => hierarchyBlock_measurable _ _
  have he' : Function.Injective (fun i => (e i:ℕ)) := Fin.val_injective.comp he
  have hcov : (μ:Measure OverlapArray) ((selectedBlock (fun i => (e i:ℕ))) ⁻¹' B)=1 := by
    rw [exchangeable_event hex _ he' hBm]
    dsimp only [B]
    rw [Set.preimage_iUnion]
    exact hierarchy_partition_cover_all hG hgg hu q hq h0 h1 hk
  have hcovr := hierarchy_partition_cover_all hG hgg hu q hq h0 h1 hr
  rw [hierarchySampleLaw_integral_block μ q (f:=fun s => f (fun i => s (e i)))
      (hf.comp (by fun_prop)) (fun s => hb _),hierarchySampleLaw_integral_block μ q hf hb]
  have hpoint : ∀ᵐ R ∂(μ:Measure OverlapArray),
      hierarchyBlockSample q (fun s => f (fun i => s (e i))) (blockOfArray r R)=
        hierarchyBlockSample q f (selectedBlock (fun i => (e i:ℕ)) R) := by
    filter_upwards [ae_full_probability μ (MeasurableSet.iUnion fun T => hierarchyEvent_measurable (treeCodes T) q) hcovr,
      ae_full_probability μ (hBm.preimage (continuous_selectedBlock _).measurable) hcov] with R hR hS
    obtain ⟨T,hT⟩ := Set.mem_iUnion.mp hR
    obtain ⟨U,hU⟩ := Set.mem_iUnion.mp hS
    rw [hierarchyBlockSample_on_event q _ T hT,hierarchyBlockSample_on_event q _ U hU]
    apply treePath_marginal_integral T U e
    · intro l i j
      exact (hT l.succ (e i) (e j)).symm.trans (hU l.succ i j)
    · exact hf
  rw [integral_congr_ae hpoint]
  have hF := hierarchyBlockSample_measurable q f
  rw [← integral_map (continuous_selectedBlock _).measurable.aemeasurable hF.aestronglyMeasurable,
    hex k _ he',blockLaw,integral_map (continuous_blockOfArray k).measurable.aemeasurable hF.aestronglyMeasurable]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma hierarchySampleLaw_product {d r : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {x : (Fin d → ℝ) → ℝ} (hx : Continuous x)
    (hb : ∀ s,0≤x s ∧ x s≤1) :
    (∫ s,∏ i : Fin r,x (s i) ∂hierarchySampleLaw μ q r)=gaussianHierarchyMoment μ q x r := by
  rw [hierarchySampleLaw_integral μ q (by fun_prop) (C:=1)]
  · apply Finset.sum_congr rfl
    intro T _
    congr 1
    rw [integral_treePathLaw T _ (by fun_prop)]
    rfl
  · intro s
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hb (s i)).1))]
    exact Finset.prod_le_one₀ (fun i _ => (hb (s i)).1) (fun i _ => (hb (s i)).2)

 

theorem hierarchy_empirical_log_tendsto {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    {x : (Fin (d+1) → ℝ) → ℝ} (hx : Continuous x) (hb : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    Tendsto (fun r => ∫ s,Real.log (1-z*((∑ i : Fin (r+1),x (s i))/(r+1:ℕ)))
      ∂hierarchySampleLaw μ q (r+1)) atTop
      (𝓝 (gaussianHierarchyRisk (fun k => overlapDiscount μ (q k.succ))
        (fun s => Real.log (1-z*x s)))) := by
  let ν (r : ℕ) := hierarchySampleLaw μ q (r+1)
  let (r : ℕ) : IsProbabilityMeasure (ν r) :=
    hierarchySampleLaw_probability hG hgg hu q hq h0 h1 (Nat.succ_pos r)
  let M (k : ℕ) := if k=0 then 1 else gaussianHierarchyMoment μ q x k
  have hM (k : ℕ) : 0≤M k ∧ M k≤1 := by
    by_cases hk : k=0
    · simp [M,hk]
    · simpa [M,hk] using gaussianHierarchyMoment_mem_unit μ q hx hb k
  have he (r k : ℕ) (e : Fin k → Fin (r+1)) (he : Function.Injective e) :
      (∫ s,∏ i,x (s (e i)) ∂ν r)=M k := by
    by_cases hk : k=0
    · subst k
      simp [M]
    have hk' := Nat.pos_of_ne_zero hk
    rw [hierarchySampleLaw_marginal_integral hG hgg hu hex q hq h0 h1 (Nat.succ_pos r) hk'
      e he (f:=fun s => ∏ i,x (s i)) (by fun_prop) (C:=1)]
    · simpa [M,hk] using hierarchySampleLaw_product μ q hx hb
    · intro s
      rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hb (s i)).1))]
      exact Finset.prod_le_one₀ (fun i _ => (hb (s i)).1) (fun i _ => (hb (s i)).2)
  have ht := empirical_log_limit_of_distinct_moments ν (fun _ s i => x (s i))
    (fun _ i => hx.measurable.comp (measurable_pi_apply i)) (fun _ s i => hb (s i)) M hM he hz
  rw [GG_gaussian_hierarchy_log_identity hG hgg hu q hq h0 h1 ha hx hb hz]
  have hs : Summable (fun n => -gaussianHierarchyMoment μ q x n/(n:ℝ)*z^n) := by
    apply Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (abs_nonneg z) hz)
    exact Eventually.of_forall (fun n => normalized_moment_bound (gaussianHierarchyMoment_mem_unit μ q hx hb n) z n)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero,div_zero,zero_mul,zero_add]
  convert ht using 2
  apply tsum_congr
  intro n
  simp only [M,Nat.add_one_ne_zero,↓reduceIte]
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma unit_average {r : ℕ} (hr : 0<r) {x : Fin r → ℝ} (hx : ∀ i,0≤x i ∧ x i≤1) :
    0≤(∑ i,x i)/(r:ℝ) ∧ (∑ i,x i)/(r:ℝ)≤1 := by
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => (hx i).1)) (by positivity),?_⟩
  apply (div_le_one (by positivity)).mpr
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => (hx i).2)

lemma affine_average {r : ℕ} (hr : 0<r) (b z : ℝ) (x : Fin r → ℝ) :
    (∑ i,b*(1-z*x i))/(r:ℝ)=b*(1-z*((∑ i,x i)/(r:ℝ))) := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hr0 : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp

lemma integral_affine_average_log {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {r : ℕ} (hr : 0<r) {x : Ω → Fin r → ℝ}
    (hx : ∀ i,Measurable (fun sample => x sample i)) (hb : ∀ sample i,0≤x sample i ∧ x sample i≤1)
    {b z : ℝ} (hbp : 0<b) (hz : |z|<1) :
    (∫ sample,Real.log ((∑ i,b*(1-z*x sample i))/(r:ℝ)) ∂ν)=
      (∫ sample,Real.log (1-z*((∑ i,x sample i)/(r:ℝ))) ∂ν)+Real.log b := by
  have hav (sample : Ω) := unit_average hr (hb sample)
  have hf : Measurable (fun sample => Real.log (1-z*((∑ i,x sample i)/(r:ℝ)))) := by
    apply Real.measurable_log.comp
    exact measurable_const.sub (((Finset.measurable_sum _ (fun i _ => hx i)).div_const _).const_mul _)
  have hi : Integrable (fun sample => Real.log (1-z*((∑ i,x sample i)/(r:ℝ)))) ν := by
    apply integrable_of_uniform_abs hf (C:=|Real.log (1-|z|)|+|Real.log (1+|z|)|)
    intro sample
    exact affine_log_bounded (x:=fun _ : Fin 0 → ℝ => (∑ i,x sample i)/(r:ℝ)) (fun _ => hav sample) hz (fun k => k.elim0)
  simp_rw [affine_average hr,Real.log_mul hbp.ne' (affine_mark_pos (hav _) hz).ne']
  rw [integral_add (integrable_const _) hi]
  simp [add_comm]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma gaussianHierarchyRisk_add_const {d : ℕ} {a : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ s,|f s|≤C) (c : ℝ) :
    gaussianHierarchyRisk a (fun s => f s+c)=gaussianHierarchyRisk a f+c := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [gaussianHierarchyRisk]
    have he (z : ℝ) := ih (fun k => ha k.succ)
      (hf.comp (continuous_finCons continuous_const continuous_id)) (fun s => hb (Fin.cons z s))
    simp only [Function.comp_def,id_eq] at he
    simp_rw [he]
    have hh := gaussianHierarchyRisk_continuous_bound (fun k => ha k.succ)
      (f:=fun z s => f (Fin.cons z s))
      (hf.comp (continuous_finCons continuous_fst continuous_snd)) (fun z s => hb (Fin.cons z s))
    exact logMean_add_const (integrable_of_uniform_abs hh.1.measurable hh.2)
      (integrable_exp_of_uniform_abs (a 0) hh.1.measurable hh.2) c

 

theorem hierarchy_empirical_positive_tendsto {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    {y : (Fin (d+1) → ℝ) → ℝ} (hy : Continuous y) {l b : ℝ} (hl : 0<l) (hlb : l<b)
    (hb : ∀ s,l≤y s ∧ y s≤b) :
    Tendsto (fun r => ∫ s,Real.log ((∑ i : Fin (r+1),y (s i))/(r+1:ℕ))
      ∂hierarchySampleLaw μ q (r+1)) atTop
      (𝓝 (gaussianHierarchyRisk (fun k => overlapDiscount μ (q k.succ)) (fun s => Real.log (y s)))) := by
  let x (s : Fin (d+1) → ℝ) := (b-y s)/(b-l)
  let z := (b-l)/b
  have hbp : 0<b := hl.trans hlb
  have hbl : 0<b-l := sub_pos.mpr hlb
  have hx : Continuous x := by unfold x; fun_prop
  have hxb (s : Fin (d+1) → ℝ) : 0≤x s ∧ x s≤1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr (hb s).2) hbl.le,
      (div_le_one hbl).mpr (by linarith [(hb s).1])⟩
  have hz : |z|<1 := by
    rw [abs_of_pos (div_pos hbl hbp)]
    exact (div_lt_one hbp).mpr (by linarith)
  have he (s : Fin (d+1) → ℝ) : y s=b*(1-z*x s) := by
    dsimp only [x,z]
    field_simp
    ring
  have hlog (s : Fin (d+1) → ℝ) : Real.log (y s)=Real.log (1-z*x s)+Real.log b := by
    rw [he,Real.log_mul hbp.ne' (affine_mark_pos (hxb s) hz).ne']
    ring
  have ht := hierarchy_empirical_log_tendsto hG hgg hu hex q hq h0 h1 ha hx hxb hz
  have hlogc : Continuous (fun s => Real.log (1-z*x s)) :=
    (continuous_const.sub (hx.const_mul z)).log (fun s => (affine_mark_pos (hxb s) hz).ne')
  have hrisk := gaussianHierarchyRisk_add_const (a:=fun k : Fin (d+1) => overlapDiscount μ (q k.succ)) (fun k => (measureReal_nonneg : 0≤overlapDiscount μ (q k.succ)))
    hlogc (affine_log_bounded hxb hz) (Real.log b)
  have hleft (r : ℕ) : (∫ s,Real.log ((∑ i : Fin (r+1),y (s i))/(r+1:ℕ)) ∂hierarchySampleLaw μ q (r+1))=
      (∫ s,Real.log (1-z*((∑ i : Fin (r+1),x (s i))/(r+1:ℕ))) ∂hierarchySampleLaw μ q (r+1))+Real.log b := by
    let := hierarchySampleLaw_probability hG hgg hu q hq h0 h1 (Nat.succ_pos r)
    have hrep : (fun s : Fin (r+1) → Fin (d+1) → ℝ => Real.log ((∑ i,y (s i))/(r+1:ℕ)))=
        (fun s => Real.log ((∑ i,b*(1-z*x (s i)))/(r+1:ℕ))) := by
      funext s
      congr 2
      exact Finset.sum_congr rfl (fun i _ => he (s i))
    rw [hrep]
    exact integral_affine_average_log _ (Nat.succ_pos r)
      (fun i => hx.measurable.comp (measurable_pi_apply i)) (fun s i => hxb (s i)) hbp hz
  simp_rw [hleft,hlog]
  rw [hrisk]
  exact ht.add_const _

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma bounded_exp_mass_derivative {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ} {C : ℝ} (hf : Measurable f) (hb : ∀ x,|f x|≤C) :
    HasDerivAt (fun a => ∫ x,Real.exp (a*f x) ∂ν) (∫ x,f x ∂ν) 0 := by
  have hC : 0≤C := by
    have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
    obtain ⟨x⟩ := this
    exact (abs_nonneg _).trans (hb x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Set.Ioo (-1:ℝ) 1) (x₀:=0) (μ:=ν) (F:=fun a x => Real.exp (a*f x))
    (F':=fun a x => Real.exp (a*f x)*f x) (bound:=fun _ => Real.exp C*C)
    (Ioo_mem_nhds (by norm_num) (by norm_num)) ?_
    (by simp)
    ?_ ?_ (integrable_const _) ?_).2
  · simpa only [zero_mul,Real.exp_zero,one_mul] using h
  · exact Eventually.of_forall (fun a => (integrable_exp_of_uniform_abs a hf hb).aestronglyMeasurable)
  · exact ((hf.const_mul 0).exp.mul hf).aestronglyMeasurable
  · filter_upwards with x a ha
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hab : |a|≤1 := (abs_lt.mpr ha).le
    have haf : a*f x≤C := (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hab (abs_nonneg _)).trans (by simpa using hb x))
    exact mul_le_mul (Real.exp_le_exp.mpr haf) (hb x) (abs_nonneg _) (Real.exp_pos _).le
  · filter_upwards with x a _
    simpa only [one_mul,id_eq] using ((hasDerivAt_id a).mul_const (f x)).exp

lemma logMean_coefficient_continuousAt_zero {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ} {C : ℝ} (hf : Measurable f) (hb : ∀ x,|f x|≤C) :
    ContinuousAt (fun a => logMean ν a f) 0 := by
  have hmass := bounded_exp_mass_derivative (ν:=ν) hf hb
  have hp : (∫ x,Real.exp (0*f x) ∂ν)=(1:ℝ) := by simp
  have hd := hmass.log (by rw [hp]; norm_num)
  rw [hp,div_one] at hd
  have hc := hd.continuousAt_div
  have he : Function.update (fun a => (Real.log (∫ x,Real.exp (a*f x) ∂ν)-
      Real.log (∫ x,Real.exp (0*f x) ∂ν))/(a-0)) 0 (∫ x,f x ∂ν)=
      (fun a => logMean ν a f) := by
    funext a
    by_cases ha : a=0
    · subst a; simp [logMean]
    · simp [logMean,ha]
  rwa [he] at hc

lemma logMean_coefficient_continuous {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ} {C : ℝ} (hf : Measurable f) (hb : ∀ x,|f x|≤C) :
    Continuous (fun a => logMean ν a f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : a=0
  · subst a; exact logMean_coefficient_continuousAt_zero hf hb
  have hmass : ContinuousAt (fun a => ∫ x,Real.exp (a*f x) ∂ν) a := by
    apply continuousAt_of_dominated (bound:=fun _ => Real.exp ((|a|+1)*C))
    · exact Eventually.of_forall fun t => ((hf.const_mul t).exp).aestronglyMeasurable
    · filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds (lt_add_one |a|))] with t ht
      filter_upwards with x
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul ht.le (hb x) (abs_nonneg _) (by positivity))
    · exact integrable_const _
    · filter_upwards with x
      exact (Real.continuous_exp.comp (continuous_id.mul_const (f x))).continuousAt
  have hc := (hmass.log (integral_exp_pos (integrable_exp_of_uniform_abs a hf hb)).ne').div continuousAt_id ha
  apply hc.congr
  filter_upwards [eventually_ne_nhds ha] with t ht
  simp [logMean,ht]

end ParisiFinite

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finiteRisk_measure (ν : Measure ι) [IsFiniteMeasure ν] (a : ℝ) (f : ι → ℝ) :
    finiteRisk (fun i => ν.real {i}) a f=logMean ν a f := by
  unfold finiteRisk logMean
  rw [integral_fintype Integrable.of_finite,integral_fintype Integrable.of_finite]
  rfl

lemma finiteRisk_coefficient_tendsto (ν : Measure ι) [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} {b : ℝ} (ha : ∀ m,0≤a m) (hab : Tendsto a atTop (𝓝 b))
    {f : ℕ → ι → ℝ} {g : ι → ℝ} (hfg : ∀ i,Tendsto (fun m => f m i) atTop (𝓝 (g i))) :
    Tendsto (fun m => finiteRisk (fun i => ν.real {i}) (a m) (f m)) atTop
      (𝓝 (finiteRisk (fun i => ν.real {i}) b g)) := by
  classical
  simp_rw [finiteRisk_measure]
  have hgb : ∀ i,|g i|≤∑ j,|g j| := fun i => Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ i)
  have hc := (logMean_coefficient_continuous (ν:=ν) (measurable_of_finite g) hgb).continuousAt.tendsto.comp hab
  have hnorm : Tendsto (fun m => ‖f m-g‖) atTop (𝓝 (0:ℝ)) := by
    simpa using ((tendsto_pi_nhds.mpr hfg).sub (tendsto_const_nhds (x:=g))).norm
  have hd : Tendsto (fun m => logMean ν (a m) (f m)-logMean ν (a m) g) atTop (𝓝 0) := by
    apply squeeze_zero_norm ?_ hnorm
    intro m
    rw [Real.norm_eq_abs]
    apply logMean_stable (ha m) Integrable.of_finite Integrable.of_finite
      Integrable.of_finite Integrable.of_finite
    intro i
    exact le_trans (norm_le_pi_norm (f m-g) i) (le_refl _) 
  have h := hd.add hc
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using h

lemma finiteHierarchyRisk_coefficient_tendsto (ν : Measure ι) [IsProbabilityMeasure ν]
    {d : ℕ} {a : ℕ → Fin d → ℝ} {b : Fin d → ℝ}
    (ha : ∀ m k,0≤a m k) (hab : ∀ k,Tendsto (fun m => a m k) atTop (𝓝 (b k)))
    (f : (Fin d → ι) → ℝ) :
    Tendsto (fun m => finiteHierarchyRisk (fun i => ν.real {i}) (a m) f) atTop
      (𝓝 (finiteHierarchyRisk (fun i => ν.real {i}) b f)) := by
  induction d with
  | zero => exact tendsto_const_nhds
  | succ d ih =>
    apply finiteRisk_coefficient_tendsto ν (fun m => ha m 0) (hab 0)
    intro i
    exact ih (fun m k => ha m k.succ) (fun k => hab k.succ) (fun s => f (Fin.cons i s))

end SKCavity

end

end OAI
