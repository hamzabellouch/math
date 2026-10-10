import Mathlib
import OAI.Probability.ParisiFinite.WeightedSumPos

namespace OAI

/-! Sum Fin Lt Nat. -/

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
open SKQAOA SKGaussian ParisiInterpolation

lemma sum_fin_lt_nat {N c : ℕ} (hc : c≤N) :
    (∑ k : Fin N,if k.val<c then (1:ℝ) else 0)=(c:ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k<c then (1:ℝ) else 0) N]
  have he : (Finset.range N).filter (fun k => k<c)=Finset.range c := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Finset.sum_filter,he]
  simp

lemma sum_grid_lt {N : ℕ} (hN : 0<N) {x : ℝ} (_hx0 : 0≤x) (hx1 : x≤1) :
    (∑ k : Fin N,if (k.val:ℝ)/(N:ℝ)<x then (1:ℝ)/(N:ℝ) else 0)=(⌈(N:ℝ)*x⌉₊:ℝ)/(N:ℝ) := by
  have hNp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hc : ⌈(N:ℝ)*x⌉₊≤N := Nat.ceil_le.mpr (by nlinarith)
  have he (k : Fin N) : ((k.val:ℝ)/(N:ℝ)<x) ↔ k.val<⌈(N:ℝ)*x⌉₊ := by
    rw [div_lt_iff₀ hNp,Nat.lt_ceil,mul_comm]
  simp_rw [he]
  have hf (k : Fin N) : (if k.val<⌈(N:ℝ)*x⌉₊ then (1:ℝ)/(N:ℝ) else 0)=
      (if k.val<⌈(N:ℝ)*x⌉₊ then (1:ℝ) else 0)/(N:ℝ) := by split_ifs <;> simp
  simp_rw [hf]
  rw [← Finset.sum_div,sum_fin_lt_nat hc]

lemma grid_covariance_error {N : ℕ} (hN : 0<N) {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) :
    |x-(∑ k : Fin N,if (k.val:ℝ)/(N:ℝ)<x then (1:ℝ)/(N:ℝ) else 0)|≤(1:ℝ)/(N:ℝ) := by
  rw [sum_grid_lt hN hx0 hx1]
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he : x-(⌈(N:ℝ)*x⌉₊:ℝ)/(N:ℝ)=((N:ℝ)*x-(⌈(N:ℝ)*x⌉₊:ℝ))/(N:ℝ) := by field_simp
  rw [he,abs_div]
  rw [show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_right (Nat.abs_sub_ceil_le (mul_nonneg (Nat.cast_nonneg N) hx0)) (Nat.cast_nonneg N)

def cavityGrid (m : ℕ) : Fin (m+2) → ℝ := Fin.cons (-2) (fun k : Fin (m+1) => (k.val:ℝ)/(m+1:ℕ))
def cavityGridVariance (m : ℕ) : Fin (m+2) → ℝ := Fin.cons 0 (fun _ : Fin (m+1) => (1:ℝ)/(m+1:ℕ))

lemma cavityGridVariance_nonneg (m : ℕ) (k : Fin (m+2)) : 0≤cavityGridVariance m k := by
  induction k using Fin.cases with
  | zero => exact le_rfl
  | succ k => exact div_nonneg zero_le_one (Nat.cast_nonneg _)

lemma cavityGridVariance_sum (m : ℕ) : (∑ k,cavityGridVariance m k)=1 := by
  rw [Fin.sum_univ_succ]
  simp only [cavityGridVariance,Fin.cons_zero,Fin.cons_succ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add]
  field_simp

lemma cavityGrid_mono (m : ℕ) : Monotone (cavityGrid m) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_rfl
    | succ j =>
      change (-2:ℝ)≤(j.val:ℝ)/(m+1:ℕ)
      have h : (0:ℝ)≤(j.val:ℝ)/(m+1:ℕ) := div_nonneg (Nat.cast_nonneg j.val) (Nat.cast_nonneg (m+1))
      linarith
  | succ i =>
    induction j using Fin.cases with
    | zero => simp at hij
    | succ j =>
      change (i.val:ℝ)/(m+1:ℕ)≤(j.val:ℝ)/(m+1:ℕ)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (Fin.succ_le_succ_iff.mp hij)

lemma cavityGrid_root (m : ℕ) : cavityGrid m 0 < -1 := by norm_num [cavityGrid]
lemma cavityGrid_last (m : ℕ) : cavityGrid m (Fin.last (m+1))<1 := by
  change (m:ℝ)/(m+1:ℕ)<1
  apply (div_lt_one (by positivity)).mpr
  exact_mod_cast Nat.lt_succ_self m

lemma cavityGrid_error (m : ℕ) {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) :
    |x-stepCovariance (cavityGrid m) (cavityGridVariance m) x|≤(1:ℝ)/(m+1:ℕ) := by
  unfold stepCovariance
  rw [Fin.sum_univ_succ]
  simp only [cavityGrid,cavityGridVariance,Fin.cons_zero,Fin.cons_succ,ite_self,zero_add]
  exact grid_covariance_error (by omega) hx0 hx1

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def gridCavityMixture (μ : ProbabilityMeasure OverlapArray) (m r : ℕ) (β : ℝ) : ℝ :=
  ∑ T : PartitionTree (m+1) r,
    (μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) (cavityGrid m))*
      cavityGramObservable (codeGramBlock (treeCodes T) (cavityGridVariance m)
        (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)) β

lemma gridCavityMixture_integral (μ : ProbabilityMeasure OverlapArray) (m r : ℕ) (β : ℝ) :
    gridCavityMixture μ m r β=
    ∫ R,∑ T : PartitionTree (m+1) r,
      (hierarchyEvent (treeCodes T) (cavityGrid m)).indicator
        (fun _ => cavityGramObservable (codeGramBlock (treeCodes T) (cavityGridVariance m)
          (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)) β) R ∂(μ:Measure OverlapArray) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T _
    rw [integral_indicator_const _ (hierarchyEvent_measurable _ _)]
    rfl
  · intro T _
    exact (integrable_const _).indicator (hierarchyEvent_measurable _ _)

theorem gridCavityMixture_error {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    (m : ℕ) {r : ℕ} (hr : 0<r) (β : ℝ) :
    |scalarCavitySample μ hr β-gridCavityMixture μ m r β|≤β^2*Real.pi/(m+1:ℕ) := by
  let E (T : PartitionTree (m+1) r) := hierarchyEvent (treeCodes T) (cavityGrid m)
  let V (T : PartitionTree (m+1) r) := cavityGramObservable (codeGramBlock (treeCodes T)
    (cavityGridVariance m) (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)) β
  let F : OverlapArray → ℝ := fun R => ∑ T : PartitionTree (m+1) r, (E T).indicator (fun _ => V T) R
  have hFi : Integrable F (μ:Measure OverlapArray) := by
    apply integrable_finsetSum
    intro T _
    exact (integrable_const _).indicator (hierarchyEvent_measurable _ _)
  let C : C(OverlapArray,ℝ) := (cavityObservable hr β).comp ⟨blockOfArray r,continuous_blockOfArray r⟩
  have hCi : Integrable C (μ:Measure OverlapArray) := C.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcover := hierarchy_partition_cover_all hG hgg hu (cavityGrid m) (cavityGrid_mono m)
    (cavityGrid_root m) (cavityGrid_last m) hr
  have hpos := GG_nonnegative_arrays hG hgg hu hex
  have hbd : ∀ᵐ R ∂(μ:Measure OverlapArray),‖C R-F R‖≤β^2*Real.pi/(m+1:ℕ) := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG,
      ae_full_probability μ isClosed_NonnegativeArrays.measurableSet hpos,
      ae_full_probability μ (MeasurableSet.iUnion fun T => hierarchyEvent_measurable (treeCodes T) (cavityGrid m)) hcover] with R hR hp hc
    obtain ⟨T,hT⟩ := Set.mem_iUnion.mp hc
    have hF : F R=V T := by
      dsimp only [F]
      rw [Finset.sum_eq_single T]
      · exact Set.indicator_of_mem hT _
      · intro U _ hUT
        apply Set.indicator_of_notMem
        intro hU
        exact (Set.disjoint_left.mp (tree_hierarchy_disjoint hUT (cavityGrid m))) hU hT
      · simp
    rw [hF,Real.norm_eq_abs]
    have h := codeCavity_error hr T (cavityGrid m) (cavityGridVariance m)
      (cavityGridVariance_nonneg m) (cavityGridVariance_sum m) (by positivity : (0:ℝ)≤1/(m+1:ℕ))
      (fun x hx0 hx1 => cavityGrid_error m hx0 hx1) hR hp hT β
    simpa only [mul_one_div,C,V,ContinuousMap.comp_apply,ContinuousMap.coe_mk] using h
  have hi := norm_integral_le_of_norm_le_const hbd
  rw [integral_sub hCi hFi] at hi
  simp only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] at hi
  rw [gridCavityMixture_integral]
  exact hi

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

def gridCavityPolynomial (m r : ℕ) (a : Fin (m+2) → ℝ) (β : ℝ) : ℝ :=
  ∑ T : PartitionTree (m+1) r,hierarchyNumerator a (treeCodes T)/((r-1).factorial:ℝ)*
    cavityGramObservable (codeGramBlock (treeCodes T) (cavityGridVariance m)
      (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)) β

lemma gridCavityPolynomial_continuous (m r : ℕ) (β : ℝ) :
    Continuous (fun a => gridCavityPolynomial m r a β) := by
  apply continuous_finsetSum
  intro T _
  exact ((continuous_hierarchyNumerator _).div_const _).mul continuous_const

lemma gridCavityMixture_eq_polynomial {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (m : ℕ) {r : ℕ} (hr : 0<r) (β : ℝ) :
    gridCavityMixture μ m r β=
      gridCavityPolynomial m r (fun k => overlapDiscount μ (cavityGrid m k)) β := by
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  have h := GG_hierarchy_EPPF hG hgg hu hr (treeCodes T) (treeCodes_nested T)
    (fun i j => by simp) (cavityGrid m) (cavityGrid_mono m) (cavityGrid_last m)
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))).mpr (by simpa only [mul_comm] using h)

lemma gridCavityPolynomial_limit {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    (β v : ℝ) (hv : Tendsto (quadraticCavitySamples μ β) atTop (𝓝 v)) :
    Tendsto (fun m => gridCavityPolynomial m ((m+1)^2)
      (fun k => overlapDiscount μ (cavityGrid m k)) β) atTop (𝓝 v) := by
  have he : Tendsto (fun m => gridCavityMixture μ m ((m+1)^2) β-quadraticCavitySamples μ β m)
      atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq,sub_zero]
    refine squeeze_zero (g:=fun m : ℕ => β^2*Real.pi/(m+1:ℕ)) (fun m => abs_nonneg _) (fun m => ?_) ?_
    · simpa only [abs_sub_comm,quadraticCavitySamples] using gridCavityMixture_error hG hgg hu hex m
        (by positivity : 0<(m+1)^2) β
    · simpa only [mul_zero,mul_one_div] using tendsto_succ_reciprocal.const_mul (β^2*Real.pi)
  have h := he.add hv
  simp only [sub_add_cancel,zero_add] at h
  have heq (m : ℕ) := gridCavityMixture_eq_polynomial hG hgg hu m (by positivity : 0<(m+1)^2) β
  simpa only [heq] using h

 

theorem exists_grid_cavity_pressure_bound {β : ℝ} (hβ : 0<β) :
    ∃ (μ : ProbabilityMeasure OverlapArray) (v : ℝ),
      (μ:Measure OverlapArray) GramArrays=1 ∧ GGIdentities μ ∧
      FiniteExchangeable μ ∧ (μ:Measure OverlapArray) UltrametricArrays=1 ∧
      (μ:Measure OverlapArray) NonnegativeArrays=1 ∧
      Tendsto (fun m => gridCavityPolynomial m ((m+1)^2)
        (fun k => overlapDiscount μ (cavityGrid m k)) β) atTop (𝓝 v) ∧
      v≤β*limitingFreeEnergy β := by
  obtain ⟨μ,v,hG,hgg,hex,hu,hv,hbound⟩ := exists_scalar_ultrametric_cavity hβ
  exact ⟨μ,v,hG,hgg,hex,hu,GG_nonnegative_arrays hG hgg hu hex,
    gridCavityPolynomial_limit hG hgg hu hex β v hv,hbound⟩

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma gaussianLaw_isGaussian : IsGaussian (gaussianLaw κ) := by
  have hX (k : κ) : HasGaussianLaw (fun x : κ → ℝ => x k) (gaussianLaw κ) := by
    refine { aemeasurable := (measurable_pi_apply k).aemeasurable, isGaussian_map := ?_ }
    change IsGaussian ((Measure.pi fun _ : κ => gaussianReal 0 1).map fun x => x k)
    rw [(measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k).map_eq]
    infer_instance
  have hi : iIndepFun (fun k (x : κ → ℝ) => x k) (gaussianLaw κ) :=
    iIndepFun_pi (X:=fun _ : κ => id) (fun _ => measurable_id.aemeasurable)
  have h := hi.hasGaussianLaw hX
  have hh := h.isGaussian_map
  change IsGaussian ((gaussianLaw κ).map id) at hh
  simpa only [Measure.map_id] using hh

def fieldCLM (A : ι → κ → ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ k,A i k • ContinuousLinearMap.proj k)

omit [Fintype ι] in
lemma fieldCLM_apply (A : ι → κ → ℝ) (x : κ → ℝ) : fieldCLM A x=field A x := by
  ext i
  simp [fieldCLM,field]

lemma field_hasGaussianLaw (A : ι → κ → ℝ) :
    HasGaussianLaw (field A) (gaussianLaw κ) := by
  let := gaussianLaw_isGaussian (κ:=κ)
  have he : field A=(fieldCLM A : (κ → ℝ) → (ι → ℝ)) := (funext (fieldCLM_apply A)).symm
  rw [he]
  exact { isGaussian_map := inferInstance }

omit [Fintype ι] in
lemma field_mean_zero (A : ι → κ → ℝ) (i : ι) :
    (∫ x,field A x i ∂gaussianLaw κ)=0 := by
  unfold field
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    have h (k : κ) : (∫ x : κ → ℝ,x k ∂gaussianLaw κ)=0 := by
      have hm := measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k
      have he := integral_map hm.aemeasurable (f:=id) aestronglyMeasurable_id
      rw [hm.map_eq] at he
      simpa [gaussianLaw] using he.symm
    simp [h]
  · intro k _
    exact (memLp_coordinate k).integrable (by norm_num) |>.const_mul _

lemma dual_apply_eq_sum [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x=∑ i,L (Pi.single i 1)*x i := by
  classical
  nth_rw 1 [← LinearMap.sum_single_apply (fun _ : ι => ℝ) x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (x i)=x i • Pi.single i (1:ℝ) := by
    ext j
    by_cases h : j=i <;> simp [h]
  rw [he,map_smul]
  simp [mul_comm]

lemma dual_field_mean_zero (L : StrongDual ℝ (ι → ℝ)) (A : ι → κ → ℝ) :
    (∫ x,L (field A x) ∂gaussianLaw κ)=0 := by
  classical
  have he : (fun x => L (field A x))=fun x => ∑ i,L (Pi.single i 1)*field A x i :=
    funext (fun x => dual_apply_eq_sum L _)
  rw [he,integral_finsetSum]
  · simp [integral_const_mul,field_mean_zero]
  · intro i _
    exact (integrable_field A i).const_mul _

lemma dual_field_variance [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (A : ι → κ → ℝ) :
    variance (fun x => L (field A x)) (gaussianLaw κ)=
      ∑ i,∑ j,L (Pi.single i 1)*L (Pi.single j 1)*kernel A i j := by
  classical
  have he : (fun x => L (field A x))=fun x => ∑ i,L (Pi.single i 1)*field A x i :=
    funext (fun x => dual_apply_eq_sum L _)
  rw [he,← covariance_self]
  · rw [covariance_fun_sum_fun_sum]
    · simp only [covariance_const_mul_left,covariance_const_mul_right,covariance_field,kernel]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro i
      exact (memLp_finsetSum Finset.univ (fun k _ => (memLp_coordinate k).const_mul (A i k))).const_mul _
    · intro i
      exact (memLp_finsetSum Finset.univ (fun k _ => (memLp_coordinate k).const_mul (A i k))).const_mul _
  · rw [← he]
    have hf : field A=(fieldCLM A : (κ → ℝ) → (ι → ℝ)) := (funext (fieldCLM_apply A)).symm
    rw [hf]
    exact (L.continuous.comp (fieldCLM A).continuous).measurable.aemeasurable

 

theorem field_law_eq_of_kernel {κ' : Type*} [Fintype κ']
    (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (h : kernel A=kernel B) :
    (gaussianLaw κ).map (field A)=(gaussianLaw κ').map (field B) := by
  classical
  apply Measure.ext_of_charFunDual
  funext L
  rw [(field_hasGaussianLaw A).charFunDual_map_eq_fun L,
    (field_hasGaussianLaw B).charFunDual_map_eq_fun L,
    dual_field_mean_zero,dual_field_mean_zero,dual_field_variance,dual_field_variance,h]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma field_continuous_any {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → κ → ℝ) :
    Continuous (field A) := by
  have he : field A=(fieldCLM A : (κ → ℝ) → (ι → ℝ)) := (funext (fieldCLM_apply A)).symm
  rw [he]
  exact (fieldCLM A).continuous

lemma integral_field_eq_of_kernel {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
    (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (h : kernel A=kernel B)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    (∫ x,f (field A x) ∂gaussianLaw κ)=(∫ x,f (field B x) ∂gaussianLaw κ') := by
  rw [← integral_map (field_continuous_any A).measurable.aemeasurable hf.aestronglyMeasurable,
    ← integral_map (field_continuous_any B).measurable.aemeasurable hf.aestronglyMeasurable,
    field_law_eq_of_kernel A B h]

 

theorem codeGaussian_marginal {d r k : ℕ} (c : Fin d → Fin r → ℕ)
    (v : Fin d → ℝ) (hv : ∀ j,0≤v j) (e : Fin k → Fin r) :
    (gaussianLaw (Σ j : Fin d,CodeLabel (c j))).map
      (fun x i => field (codeGaussianCoeff c v) x (e i))=
    (gaussianLaw (Σ j : Fin d,CodeLabel (fun i => c j (e i)))).map
      (field (codeGaussianCoeff (fun j i => c j (e i)) v)) := by
  apply field_law_eq_of_kernel
  funext i l
  change kernel (codeGaussianCoeff c v) (e i) (e l)=_
  simp only [kernel_codeGaussianCoeff c v hv,
    kernel_codeGaussianCoeff (fun j i => c j (e i)) v hv]

lemma codeGaussian_integral_marginal {d r k : ℕ} (c : Fin d → Fin r → ℕ)
    (v : Fin d → ℝ) (hv : ∀ j,0≤v j) (e : Fin k → Fin r)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) :
    (∫ x,f (fun i => field (codeGaussianCoeff c v) x (e i))
      ∂gaussianLaw (Σ j : Fin d,CodeLabel (c j)))=
    (∫ x,f (field (codeGaussianCoeff (fun j i => c j (e i)) v) x)
      ∂gaussianLaw (Σ j : Fin d,CodeLabel (fun i => c j (e i)))) := by
  apply integral_field_eq_of_kernel
  · funext i l
    change kernel (codeGaussianCoeff c v) (e i) (e l)=_
    simp only [kernel_codeGaussianCoeff c v hv,
      kernel_codeGaussianCoeff (fun j i => c j (e i)) v hv]
  · exact hf

lemma codeGaussian_law_of_same_partition {d r : ℕ}
    (c b : Fin d → Fin r → ℕ) (v : Fin d → ℝ) (hv : ∀ j,0≤v j)
    (he : ∀ j i l,c j i=c j l ↔ b j i=b j l) :
    (gaussianLaw (Σ j : Fin d,CodeLabel (c j))).map (field (codeGaussianCoeff c v))=
    (gaussianLaw (Σ j : Fin d,CodeLabel (b j))).map (field (codeGaussianCoeff b v)) := by
  apply field_law_eq_of_kernel
  funext i l
  simp only [kernel_codeGaussianCoeff c v hv,kernel_codeGaussianCoeff b v hv,he]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

def gaussianQuantizer (m : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) m

abbrev GaussianQuantizerLabel (m : ℕ) := ↥(gaussianQuantizer m).range

def gaussianQuantizerIndex (m : ℕ) (x : ℝ) : GaussianQuantizerLabel m :=
  ⟨gaussianQuantizer m x,(gaussianQuantizer m).mem_range_self x⟩

lemma gaussianQuantizerIndex_measurable (m : ℕ) : Measurable (gaussianQuantizerIndex m) :=
  (gaussianQuantizer m).measurable.subtype_mk

lemma gaussianQuantizer_tendsto (x : ℝ) :
    Tendsto (fun m => gaussianQuantizer m x) atTop (𝓝 x) := by
  exact SimpleFunc.tendsto_approxOn (f:=id) (s:=(Set.univ : Set ℝ)) (y₀:=0) measurable_id (Set.mem_univ _) (by simp)

def gaussianQuantizerLaw (m : ℕ) : Measure (GaussianQuantizerLabel m) :=
  (gaussianReal 0 1).map (gaussianQuantizerIndex m)

instance gaussianQuantizerLaw_probability (m : ℕ) : IsProbabilityMeasure (gaussianQuantizerLaw m) := by
  unfold gaussianQuantizerLaw
  infer_instance

def gaussianQuantizerWeight (m : ℕ) (i : GaussianQuantizerLabel m) : ℝ :=
  (gaussianQuantizerLaw m).real {i}

lemma gaussianQuantizerWeight_nonneg (m : ℕ) (i : GaussianQuantizerLabel m) :
    0≤gaussianQuantizerWeight m i := measureReal_nonneg

lemma gaussianQuantizerWeight_sum (m : ℕ) : (∑ i,gaussianQuantizerWeight m i)=1 := by
  simp [gaussianQuantizerWeight]

lemma gaussianQuantizer_quadrature {κ : Type*} [Fintype κ] [DecidableEq κ] (m : ℕ)
    (F : (κ → GaussianQuantizerLabel m) → ℝ) :
    (∫ z,F (fun i => gaussianQuantizerIndex m (z i)) ∂gaussianLaw κ)=
      ∑ s,(∏ i,gaussianQuantizerWeight m (s i))*F s := by
  classical
  let ν : Measure (κ → GaussianQuantizerLabel m) := Measure.pi (fun _ => gaussianQuantizerLaw m)
  have hm : Measurable (fun z : κ → ℝ => fun i => gaussianQuantizerIndex m (z i)) :=
    Measurable.of_eval (fun i => (gaussianQuantizerIndex_measurable m).comp (measurable_pi_apply i))
  have hmap : (gaussianLaw κ).map (fun z i => gaussianQuantizerIndex m (z i))=ν := by
    exact Measure.pi_map_pi (fun _ => (gaussianQuantizerIndex_measurable m).aemeasurable)
  have hF : Integrable F ν := Integrable.of_finite
  rw [← integral_map hm.aemeasurable (by rw [hmap]; exact hF.aestronglyMeasurable),hmap,integral_fintype hF]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  simp [ν,measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod,gaussianQuantizerWeight]

 

theorem gaussianQuantizer_bounded_continuous {κ : Type*} [Fintype κ] [DecidableEq κ]
    (F : (κ → ℝ) → ℝ) (hF : Continuous F) {C : ℝ} (hC : ∀ x,|F x|≤C) :
    Tendsto (fun m => ∑ s : κ → GaussianQuantizerLabel m,
      (∏ i,gaussianQuantizerWeight m (s i))*F (fun i => (s i).val)) atTop
      (𝓝 (∫ z,F z ∂gaussianLaw κ)) := by
  have he (m : ℕ) : (∑ s : κ → GaussianQuantizerLabel m,
      (∏ i,gaussianQuantizerWeight m (s i))*F (fun i => (s i).val))=
      ∫ z,F (fun i => gaussianQuantizer m (z i)) ∂gaussianLaw κ :=
    (gaussianQuantizer_quadrature m (fun s => F (fun i => (s i).val))).symm
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro m
    exact (hF.measurable.comp (Measurable.of_eval (fun i =>
      (gaussianQuantizer m).measurable.comp (measurable_pi_apply i)))).aestronglyMeasurable
  · exact integrable_const C
  · intro m
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hC (fun i => gaussianQuantizer m (x i))
  · filter_upwards with x
    exact hF.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun i => gaussianQuantizer_tendsto (x i)))

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

@[reducible] def TreeNode : {d r : ℕ} → PartitionTree d r → Type
  | 0,_,_ => Empty
  | _+1,_,⟨P,T⟩ => Σ j : Fin P.length,Unit ⊕ TreeNode (T j)

instance treeNodeFintype {d r : ℕ} (T : PartitionTree d r) : Fintype (TreeNode T) := by
  induction d generalizing r with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih =>
    rcases T with ⟨P,T⟩
    let (j : Fin P.length) : Fintype (TreeNode (T j)) := ih (T j)
    exact inferInstanceAs (Fintype (Σ j : Fin P.length,Unit ⊕ TreeNode (T j)))
instance treeNodeDecidableEq {d r : ℕ} (T : PartitionTree d r) : DecidableEq (TreeNode T) := Classical.decEq _

def treeNodePath : {d r : ℕ} → (T : PartitionTree d r) → Fin r → Fin d → TreeNode T
  | 0,_,_,_ => fun k => Fin.elim0 k
  | _+1,_,⟨P,T⟩,i =>
    let j := P.equivSigma.symm i
    Fin.cases ⟨j.1,Sum.inl ()⟩ (fun k => ⟨j.1,Sum.inr (treeNodePath (T j.1) j.2 k)⟩)

lemma treeNodePath_emb {d r : ℕ} (P : OrderedFinpartition r) (T : ∀ j,PartitionTree d (P.partSize j))
    (j : Fin P.length) (i : Fin (P.partSize j)) (k : Fin (d+1)) :
    treeNodePath (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) (P.emb j i) k=
      Fin.cases ⟨j,Sum.inl ()⟩ (fun l => ⟨j,Sum.inr (treeNodePath (T j) i l)⟩) k := by
  simp only [treeNodePath]
  rw [show P.equivSigma.symm (P.emb j i)=⟨j,i⟩ from P.equivSigma.symm_apply_apply ⟨j,i⟩]

lemma treeNodePath_eq_iff {d r : ℕ} (T : PartitionTree d r) (i j : Fin r) (k : Fin d) :
    treeNodePath T i k=treeNodePath T j k ↔ treeCodes T k.succ i=treeCodes T k.succ j := by
  induction d generalizing r with
  | zero => exact Fin.elim0 k
  | succ d ih =>
    rcases T with ⟨P,T⟩
    obtain ⟨⟨u,i⟩,rfl⟩ := P.equivSigma.surjective i
    obtain ⟨⟨v,j⟩,rfl⟩ := P.equivSigma.surjective j
    change treeNodePath _ (P.emb u i) k=treeNodePath _ (P.emb v j) k ↔
      treeCodes (⟨P,T⟩ : PartitionTree (d+1) r) k.succ (P.emb u i)=
        treeCodes (⟨P,T⟩ : PartitionTree (d+1) r) k.succ (P.emb v j)
    rw [treeNodePath_emb,treeNodePath_emb]
    simp only [treeCodes_succ,splitCode_emb,Nat.pair_eq_pair]
    by_cases huv : u=v
    · subst v
      induction k using Fin.cases with
      | zero => simp [treeCodes_root]
      | succ k => simpa using ih (T u) i j k
    · have hv : u.val≠v.val := fun h => huv (Fin.ext h)
      constructor
      · intro h
        have he := congrArg Sigma.fst h
        have huv' : u=v := by cases k using Fin.cases <;> simpa using he
        exact False.elim (huv huv')
      · intro h
        exact False.elim (hv h.1)

def treeDrawToNodes {ι : Type*} : {d r : ℕ} → (T : PartitionTree d r) → TreeDraw ι T → TreeNode T → ι
  | 0,_,_,_ => fun x => Empty.elim x
  | _+1,_,⟨_,T⟩,s => fun ⟨j,x⟩ => Sum.casesOn x (fun _ => (s j).1) (treeDrawToNodes (T j) (s j).2)

def treeNodesToDraw {ι : Type*} : {d r : ℕ} → (T : PartitionTree d r) → (TreeNode T → ι) → TreeDraw ι T
  | 0,_,_,_ => PUnit.unit
  | _+1,_,⟨_,T⟩,s => fun j => (s ⟨j,Sum.inl ()⟩,treeNodesToDraw (T j) (fun x => s ⟨j,Sum.inr x⟩))

lemma treeNodesToDraw_toNodes {ι : Type*} {d r : ℕ} (T : PartitionTree d r) (s : TreeDraw ι T) :
    treeNodesToDraw T (treeDrawToNodes T s)=s := by
  induction d generalizing r with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rcases T with ⟨P,T⟩
    funext j
    apply Prod.ext
    · rfl
    · exact ih (T j) (s j).2

lemma treeDrawToNodes_toDraw {ι : Type*} {d r : ℕ} (T : PartitionTree d r) (s : TreeNode T → ι) :
    treeDrawToNodes T (treeNodesToDraw T s)=s := by
  induction d generalizing r with
  | zero => funext x; exact Empty.elim x
  | succ d ih =>
    rcases T with ⟨P,T⟩
    funext ⟨j,x⟩
    cases x with
    | inl x => cases x; rfl
    | inr x => exact congrFun (ih (T j) (fun y => s ⟨j,Sum.inr y⟩)) x

def treeDrawEquivNodes (ι : Type*) {d r : ℕ} (T : PartitionTree d r) : TreeDraw ι T ≃ (TreeNode T → ι) where
  toFun := treeDrawToNodes T
  invFun := treeNodesToDraw T
  left_inv := treeNodesToDraw_toNodes T
  right_inv := treeDrawToNodes_toDraw T

lemma treeDrawToNodes_path {ι : Type*} [Fintype ι] {d r : ℕ} (T : PartitionTree d r) (s : TreeDraw ι T)
    (i : Fin r) (k : Fin d) : treeDrawToNodes T s (treeNodePath T i k)=treeDrawPath T s i k := by
  induction d generalizing r with
  | zero => exact Fin.elim0 k
  | succ d ih =>
    rcases T with ⟨P,T⟩
    obtain ⟨⟨j,i⟩,rfl⟩ := P.equivSigma.surjective i
    change treeDrawToNodes _ s (treeNodePath _ (P.emb j i) k)=treeDrawPath _ s (P.emb j i) k
    rw [treeNodePath_emb,treeDrawPath_emb]
    induction k using Fin.cases with
    | zero => rfl
    | succ k => exact ih (T j) (s j).2 i k

lemma treeDrawToNodes_weight {ι : Type*} [Fintype ι] {d r : ℕ} (T : PartitionTree d r)
    (w : ι → ℝ) (s : TreeDraw ι T) : (∏ n,w (treeDrawToNodes T s n))=treeDrawWeight w T s := by
  induction d generalizing r with
  | zero => simp [treeDrawWeight]
  | succ d ih =>
    rcases T with ⟨P,T⟩
    change (∏ n : Σ j : Fin P.length,Unit ⊕ TreeNode (T j),w (treeDrawToNodes _ s n))=_
    rw [Fintype.prod_sigma]
    simp only [Fintype.prod_sum_type,treeDrawToNodes,Fintype.prod_unique,ih]
    rfl

lemma treeMarkMoment_node_sum {ι : Type*} [Fintype ι] {d r : ℕ} (T : PartitionTree d r)
    (w : ι → ℝ) (x : (Fin d → ι) → ℝ) :
    treeMarkMoment w x T=∑ s : TreeNode T → ι,(∏ n,w (s n))*∏ i,x (fun k => s (treeNodePath T i k)) := by
  rw [← treeDraw_product w x T,← (treeDrawEquivNodes ι T).sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  simp only [treeDrawEquivNodes,Equiv.coe_fn_mk,treeDrawToNodes_weight,treeDrawToNodes_path]

end SKCavity

end

end OAI
