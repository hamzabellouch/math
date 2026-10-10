import Mathlib
import OAI.Probability.ParisiFinite.IntegrableExpField

namespace OAI

/-! Expected Reindex States. -/

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma expected_reindex_states {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    (e : ι' ≃ ι) (A : ι → κ → ℝ) : expected (fun s => A (e s))=expected A := by
  unfold expected logPartition partition
  congr 1
  ext z
  congr 1
  exact e.sum_comp (fun s => Real.exp (field A z s))

lemma expected_kernel_distance_le {ι κ κ' : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Fintype κ'] (A : ι → κ → ℝ) (B : ι → κ' → ℝ)
    {M : ℝ} (hM : 0≤M) (h : ∀ i j,|kernel B i j-kernel A i j|≤M) :
    |expected B-expected A|≤Real.pi*M := by
  have hi (i j : ι) : |ParisiInterpolation.increment B i j-ParisiInterpolation.increment A i j|≤4*M := by
    rw [increment_eq_kernel,increment_eq_kernel]
    have he : kernel B i i+kernel B j j-2*kernel B i j-(kernel A i i+kernel A j j-2*kernel A i j)=
        (kernel B i i-kernel A i i)+(kernel B j j-kernel A j j)-2*(kernel B i j-kernel A i j) := by ring
    rw [he]
    have h1 := abs_sub ((kernel B i i-kernel A i i)+(kernel B j j-kernel A j j)) (2*(kernel B i j-kernel A i j))
    have h2 := abs_add_le (kernel B i i-kernel A i i) (kernel B j j-kernel A j j)
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h1
    linarith [h i i,h j j,h i j]
  exact (expected_difference_le A B (by positivity : 0≤4*M) hi).trans_eq (by ring)

def idealSite (n : ℕ) (β : ℝ) : Configuration n → (Fin 1 → Fin n) → ℝ :=
  fun σ k => β*pSpinCoeff n 1 σ k

def idealCorrection (n : ℕ) (β : ℝ) : Configuration n → (Fin 2 → Fin n) → ℝ :=
  fun σ k => (β/Real.sqrt 2)*pSpinCoeff n 2 σ k

lemma kernel_idealSite {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    kernel (idealSite n β) σ τ=β^2*overlap σ τ := by
  unfold idealSite
  rw [kernel_scale,pSpinCoeff_kernel hn,pow_one]

lemma kernel_idealCorrection {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    kernel (idealCorrection n β) σ τ=β^2/2*(overlap σ τ)^2 := by
  unfold idealCorrection
  rw [kernel_scale,pSpinCoeff_kernel hn,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

lemma kernel_cavityDoubledCoeff {ι κ κ' : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype κ']
    (A : ι → κ → ℝ) (B : ι → κ' → ℝ) (s t : ι × Bool) :
    kernel (cavityDoubledCoeff A B) s t=kernel A s.1 t.1+signBool s.2*signBool t.2*kernel B s.1 t.1 := by
  rw [cavityDoubledCoeff,kernel_independent]
  congr 1
  simp only [kernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

def actualSite (n : ℕ) (β : ℝ) : Configuration n → Fin n → ℝ := fun σ i => β*cavityScale n*spin σ i

def actualCorrection (n : ℕ) (β : ℝ) : Configuration n → Edge n → ℝ := fun σ e => β*cavityScale n*skCoeff n σ e

lemma kernel_actualSite {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    kernel (actualSite n β) σ τ=β^2*((n:ℝ)/(n+1))*overlap σ τ := by
  have he : kernel (actualSite n β) σ τ=β^2*cavityScale n^2*overlapSum σ τ := by
    simp only [kernel,actualSite,overlapSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,cavityScale_sq,overlap]
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

lemma kernel_actualCorrection {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    kernel (actualCorrection n β) σ τ=β^2/(2*((n:ℝ)+1))*((n:ℝ)*(overlap σ τ)^2-1) := by
  unfold actualCorrection
  rw [kernel_scale,kernel,coeff_covariance hn,mul_pow,cavityScale_sq]
  unfold overlap
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

lemma actualSite_kernel_error {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    |kernel (actualSite n β) σ τ-kernel (idealSite n β) σ τ|≤β^2/((n:ℝ)+1) := by
  rw [kernel_actualSite hn,kernel_idealSite hn]
  have he : β^2*((n:ℝ)/(n+1))*overlap σ τ-β^2*overlap σ τ=-(β^2/((n:ℝ)+1))*overlap σ τ := by
    field_simp; ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤β^2/((n:ℝ)+1))]
  exact mul_le_of_le_one_right (by positivity) (abs_overlap_le_one σ τ)

lemma actualCorrection_kernel_error {n : ℕ} (hn : 0<n) (β : ℝ) (σ τ : Configuration n) :
    |kernel (actualCorrection n β) σ τ-kernel (idealCorrection n β) σ τ|≤β^2/((n:ℝ)+1) := by
  rw [kernel_actualCorrection hn,kernel_idealCorrection hn]
  have he : β^2/(2*((n:ℝ)+1))*((n:ℝ)*(overlap σ τ)^2-1)-β^2/2*(overlap σ τ)^2=
      -(β^2/(2*((n:ℝ)+1)))*((overlap σ τ)^2+1) := by field_simp; ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤β^2/(2*((n:ℝ)+1))),abs_of_nonneg (by positivity : 0≤(overlap σ τ)^2+1)]
  have h := (sq_le_one_iff_abs_le_one (overlap σ τ)).mpr (abs_overlap_le_one σ τ)
  have hh := mul_le_mul_of_nonneg_left (by linarith : (overlap σ τ)^2+1≤2) (by positivity : 0≤β^2/(2*((n:ℝ)+1)))
  exact hh.trans_eq (by field_simp)

variable {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
lemma mixedCavity_doubled (n : ℕ) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    expected (mixedCavityCoeff n d β x)=
      expected (cavityDoubledCoeff (mixedCoeff n d (β*coreScale n) x) (actualSite n β)) := by
  let e : (Configuration n × Bool) ≃ Configuration (n+1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Bool))
  rw [mixedCavity_split,← expected_reindex_states e]
  apply expected_logPartition_eq_of_kernel
  intro s t
  rw [kernel_cavityDoubledCoeff]
  change kernel (independentCoeff (fun s => mixedCoeff n d (β*coreScale n) x (restrictLeft (e s)))
    (fun s => siteCoeff n β (e s))) s t=_
  rw [kernel_independent]
  have he (s : Configuration n × Bool) : restrictLeft (e s)=s.1 := restrictLeft_snoc s.1 s.2
  have hs (s : Configuration n × Bool) : spin (e s) (Fin.last n)= -signBool s.2 := by
    change spin (Fin.snoc s.1 s.2) (Fin.last n)= -signBool s.2
    cases s.2 <;> simp [spin,signBool]
  simp only [he,kernel,siteCoeff,hs,actualSite,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

def idealCavity {n : ℕ} {κ : Type*} [Fintype κ] (A : Configuration n → κ → ℝ) (β : ℝ) : ℝ :=
  expected (cavityDoubledCoeff A (idealSite n β))-expected (independentCoeff A (idealCorrection n β))

 

omit [DecidableEq K] in
theorem mixedIncrement_ideal_error {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    |mixedIncrement n d β x-idealCavity (mixedCoeff n d (β*coreScale n) x) β|≤
      2*Real.pi*β^2/((n:ℝ)+1) := by
  let A := mixedCoeff n d (β*coreScale n) x
  have h1 : |expected (cavityDoubledCoeff A (actualSite n β))-expected (cavityDoubledCoeff A (idealSite n β))|≤
      Real.pi*(β^2/((n:ℝ)+1)) := by
    apply expected_kernel_distance_le _ _ (by positivity)
    intro s t
    rw [kernel_cavityDoubledCoeff,kernel_cavityDoubledCoeff,add_sub_add_left_eq_sub,← mul_sub,abs_mul,
      abs_mul,abs_signBool,abs_signBool,one_mul,one_mul]
    exact actualSite_kernel_error hn β s.1 t.1
  have h2 : |expected (independentCoeff A (actualCorrection n β))-expected (independentCoeff A (idealCorrection n β))|≤
      Real.pi*(β^2/((n:ℝ)+1)) := by
    apply expected_kernel_distance_le _ _ (by positivity)
    intro s t
    rw [kernel_independent,kernel_independent,add_sub_add_left_eq_sub]
    exact actualCorrection_kernel_error hn β s t
  unfold mixedIncrement idealCavity
  rw [mixedCavity_doubled,mixed_core_correction]
  change |(expected (cavityDoubledCoeff A (actualSite n β))-expected (independentCoeff A (actualCorrection n β)))-
    (expected (cavityDoubledCoeff A (idealSite n β))-expected (independentCoeff A (idealCorrection n β)))|≤_
  have he : ∀ a b c d : ℝ,(a-b)-(c-d)=(a-c)-(b-d) := by intros; ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma blockOfReplicas_Gram {n r : ℕ} (hn : 0<n) (σ : Fin r → Configuration n) :
    blockOfReplicas σ ∈ GramBlock r := by
  refine ⟨fun i j => Subtype.ext (overlap_symm _ _),fun i => overlap_self hn _,?_⟩
  intro c
  change 0≤∑ i,∑ j,c i*c j*overlap (σ i) (σ j)
  rw [overlap_quadratic]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg n)

 

def cavityObservable {r : ℕ} (hr : 0<r) (β : ℝ) : C(OverlapBlock r,ℝ) :=
  ((ContinuousMap.mk _ (continuous_cavityGramObservable hr β)).exists_extension
    (isClosed_GramBlock r).isClosedEmbedding_subtypeVal).choose

lemma cavityObservable_on_Gram {r : ℕ} (hr : 0<r) (β : ℝ) (T : GramBlock r) :
    cavityObservable hr β T.val=cavityGramObservable T β := by
  have h := ((ContinuousMap.mk _ (continuous_cavityGramObservable hr β)).exists_extension
    (isClosed_GramBlock r).isClosedEmbedding_subtypeVal).choose_spec
  exact congrArg (fun f : C(GramBlock r,ℝ) => f T) h

lemma sample_ideal_cosh {n r : ℕ} (hn : 0<n) (hr : 0<r) (β : ℝ) (σ : Fin r → Configuration n) :
    sampleCoshPressure (idealSite n β) σ=coshGramPressure ⟨blockOfReplicas σ,blockOfReplicas_Gram hn σ⟩ β := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  unfold sampleCoshPressure coshGramPressure
  congr 1
  apply expected_logPartition_eq_of_kernel
  intro s t
  rw [kernel_coshGramCoeff]
  have he : kernel (fun s : Fin r × Bool => fun k => signBool s.2*idealSite n β (σ s.1) k) s t=
      signBool s.2*signBool t.2*kernel (idealSite n β) (σ s.1) (σ t.1) := by
    simp only [kernel,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,kernel_idealSite hn]
  simp only [blockOfReplicas,mul_assoc]

lemma sample_ideal_square {n r : ℕ} (hn : 0<n) (hr : 0<r) (β : ℝ) (σ : Fin r → Configuration n) :
    samplePressure (idealCorrection n β) σ=squareGramPressure ⟨blockOfReplicas σ,blockOfReplicas_Gram hn σ⟩ β := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  unfold samplePressure squareGramPressure
  congr 1
  apply expected_logPartition_eq_of_kernel
  intro s t
  rw [kernel_squareGramCoeff]
  exact kernel_idealCorrection hn β (σ s) (σ t)

lemma cavityObservable_replicas {n r : ℕ} (hn : 0<n) (hr : 0<r) (β : ℝ) (σ : Fin r → Configuration n) :
    cavityObservable hr β (blockOfReplicas σ)=sampleCoshPressure (idealSite n β) σ-samplePressure (idealCorrection n β) σ := by
  rw [sample_ideal_cosh hn hr,sample_ideal_square hn hr]
  exact cavityObservable_on_Gram hr β ⟨blockOfReplicas σ,blockOfReplicas_Gram hn σ⟩

def cavitySampleError (β t : ℝ) (r : ℕ) : ℝ :=
  (4*Real.exp (2*β^2))*(t/(r:ℝ))+t⁻¹+Real.exp (β^2)*(t/(r:ℝ)+t⁻¹)

 

theorem cavityObservable_ideal_error {n r : ℕ} {κ : Type*} [Fintype κ]
    (hn : 0<n) (hr : 0<r) (A : Configuration n → κ → ℝ) (β : ℝ) {t : ℝ} (ht : 0<t) :
    |averagedReplica A (fun σ : Fin r → Configuration n => cavityObservable hr β (blockOfReplicas σ))-idealCavity A β|≤
      cavitySampleError β t r := by
  simp_rw [cavityObservable_replicas hn hr]
  rw [averagedReplica_sub]
  have h1 := averaged_gaussian_cosh_sample_error hr A (idealSite n β)
    (fun σ => by rw [kernel_idealSite hn,overlap_self hn,mul_one]) ht
  have h2 := averaged_gaussian_sample_error hr A (idealCorrection n β)
    (fun σ => by rw [kernel_idealCorrection hn,overlap_self hn,one_pow,mul_one]) ht
  have he : ∀ a b c d z : ℝ,(a-b)-(c-d)=(a-(c-z))-(b-(d-z)) := by intros; ring
  unfold idealCavity
  rw [he _ _ _ _ (expected A)]
  have hh := (abs_sub _ _).trans (add_le_add h1 h2)
  simpa only [cavitySampleError,show 2*(β^2/2)=β^2 by ring] using hh

variable {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
theorem cavityObservable_actual_error {n r q : ℕ} (hn : 0<n) (hr : 0<r) (hrq : r≤q+1)
    (d : K → ℕ) (β : ℝ) (x : K → ℝ) {t : ℝ} (ht : 0<t) :
    |(∫ R,cavityObservable hr β (blockOfArray r R) ∂(fieldOverlapLaw (t:=q)
      (mixedCoeff n d (β*coreScale n) x) : Measure _))-mixedIncrement n d β x|≤
        cavitySampleError β t r+2*Real.pi*β^2/((n:ℝ)+1) := by
  rw [integral_fieldOverlapLaw_block hrq]
  have h1 := cavityObservable_ideal_error hn hr (mixedCoeff n d (β*coreScale n) x) β ht
  have h2 := mixedIncrement_ideal_error hn d β x
  rw [abs_sub_comm] at h2
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma compatibleValue_lower {β : ℝ} (hβ : 0<β) (m : ℕ) :
    Real.log 2-Real.pi*β^2/2≤compatibleValue hβ m :=
  mixedIncrement_lower (compatible_spec hβ m).2.1 _ _ _

lemma compatibleValue_upper {β : ℝ} (hβ : 0<β) (m : ℕ) :
    compatibleValue hβ m≤Real.log 2+Real.pi*β^2 := mixedIncrement_upper _ _ _ _

lemma exists_value_subsequence {β : ℝ} (hβ : 0<β) (φ : ℕ → ℕ) :
    ∃ (v : ℝ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Tendsto (fun k => compatibleValue hβ (φ (ψ k))) atTop (𝓝 v) := by
  let u : ℕ → Set.Icc (Real.log 2-Real.pi*β^2/2) (Real.log 2+Real.pi*β^2) :=
    fun k => ⟨compatibleValue hβ (φ k),compatibleValue_lower hβ _,compatibleValue_upper hβ _⟩
  obtain ⟨v,ψ,hψ,hv⟩ := CompactSpace.tendsto_subseq u
  exact ⟨v.val,ψ,hψ,continuous_subtype_val.tendsto v |>.comp hv⟩

lemma compatibleValue_limit_le {β v : ℝ} (hβ : 0<β) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hv : Tendsto (fun k => compatibleValue hβ (φ k)) atTop (𝓝 v)) :
    v≤β*limitingFreeEnergy β := by
  have hh := le_of_tendsto_of_tendsto' hv
    (tendsto_const_nhds.add (tendsto_succ_reciprocal.comp hφ.tendsto_atTop))
      (fun k => compatibleValue_le hβ (φ k))
  simpa only [add_zero] using hh

lemma tendsto_compatible_correction {β : ℝ} (hβ : 0<β) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun k => 2*Real.pi*β^2/((compatibleSize hβ (φ k):ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun k => compatibleSize hβ (φ k)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ _).trans (compatible_spec hβ (φ k)).1) hφ.tendsto_atTop
  have hd : Tendsto (fun k => ((compatibleSize hβ (φ k)+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun k => Nat.le_succ (compatibleSize hβ (φ k))) hn)
  have hi := (tendsto_inv_atTop_zero.comp hd).const_mul (2*Real.pi*β^2)
  simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_zero,Function.comp_def] using hi

def scalarCavitySample (μ : ProbabilityMeasure OverlapArray) {r : ℕ} (hr : 0<r) (β : ℝ) : ℝ :=
  ∫ R,cavityObservable hr β (blockOfArray r R) ∂(μ : Measure _)

 

theorem scalarCavitySample_limit_error {β v : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (hv : Tendsto (fun k => compatibleValue hβ (φ k)) atTop (𝓝 v))
    {r : ℕ} (hr : 0<r) {t : ℝ} (ht : 0<t) :
    |scalarCavitySample μ hr β-v|≤cavitySampleError β t r := by
  let F : C(OverlapArray,ℝ) := (cavityObservable hr β).comp ⟨blockOfArray r,continuous_blockOfArray r⟩
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hμ
  have hh : ∀ᶠ k in atTop,
      |(∫ R,F R ∂(compatibleLaw hβ (φ k) : Measure _))-compatibleValue hβ (φ k)|≤
        cavitySampleError β t r+2*Real.pi*β^2/((compatibleSize hβ (φ k):ℝ)+1) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop r)] with k hk
    exact cavityObservable_actual_error (compatible_spec hβ (φ k)).2.1 hr (by omega) _ β _ ht
  have h := le_of_tendsto_of_tendsto ((hF.sub hv).abs)
    (tendsto_const_nhds.add (tendsto_compatible_correction hβ hφ)) hh
  simpa only [add_zero,scalarCavitySample,F,ContinuousMap.comp_apply,ContinuousMap.coe_mk] using h

lemma cavitySampleError_square (β : ℝ) (m : ℕ) :
    cavitySampleError β (m+1:ℕ) ((m+1)^2)=
      (4*Real.exp (2*β^2)+1+2*Real.exp (β^2))/(m+1:ℕ) := by
  have hm : ((m+1:ℕ):ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  unfold cavitySampleError
  push_cast
  field_simp
  ring

def quadraticCavitySamples (μ : ProbabilityMeasure OverlapArray) (β : ℝ) (m : ℕ) : ℝ :=
  scalarCavitySample μ (by positivity : 0<(m+1)^2) β

lemma tendsto_cavitySampleError_square (β : ℝ) :
    Tendsto (fun m : ℕ => cavitySampleError β (m+1:ℕ) ((m+1)^2)) atTop (𝓝 0) := by
  simp_rw [cavitySampleError_square]
  convert tendsto_succ_reciprocal.const_mul (4*Real.exp (2*β^2)+1+2*Real.exp (β^2)) using 1 <;>
    simp only [mul_zero,mul_one_div]

lemma quadraticCavitySamples_limit {β v : ℝ} (hβ : 0<β) {μ : ProbabilityMeasure OverlapArray}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hμ : Tendsto (fun k => compatibleLaw hβ (φ k)) atTop (𝓝 μ))
    (hv : Tendsto (fun k => compatibleValue hβ (φ k)) atTop (𝓝 v)) :
    Tendsto (quadraticCavitySamples μ β) atTop (𝓝 v) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun m => abs_nonneg _) (fun m =>
    scalarCavitySample_limit_error hβ hφ hμ hv (by positivity) (by positivity : (0:ℝ)<(m+1:ℕ)))
      (tendsto_cavitySampleError_square β)

 

theorem exists_scalar_ultrametric_cavity {β : ℝ} (hβ : 0<β) :
    ∃ (μ : ProbabilityMeasure OverlapArray) (v : ℝ),
      (μ : Measure OverlapArray) GramArrays=1 ∧ GGIdentities μ ∧ FiniteExchangeable μ ∧
      (μ : Measure OverlapArray) UltrametricArrays=1 ∧
      Tendsto (quadraticCavitySamples μ β) atTop (𝓝 v) ∧ v≤β*limitingFreeEnergy β := by
  obtain ⟨μ,φ,hφ,hμ,hG,hgg,hex,hu,_⟩ := exists_compatible_ultrametric_limit hβ
  obtain ⟨v,ψ,hψ,hv⟩ := exists_value_subsequence hβ φ
  have hφψ := hφ.comp hψ
  have hμ' := hμ.comp hψ.tendsto_atTop
  exact ⟨μ,v,hG,hgg,hex,hu,quadraticCavitySamples_limit hβ hφψ hμ' hv,
    compatibleValue_limit_le hβ hφψ hv⟩

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def codeLabels {r : ℕ} (c : Fin r → ℕ) : Finset ℕ := Finset.univ.image c

def labelCount {r : ℕ} (c : Fin r → ℕ) (x : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => c i=x)).card

lemma codeLabels_mem {r : ℕ} (c : Fin r → ℕ) (x : ℕ) :
    x∈codeLabels c ↔ ∃ i,c i=x := by simp [codeLabels]

lemma labelCount_eq_clusterCount {r : ℕ} (c : Fin r → ℕ) (i : Fin r) :
    labelCount c (c i)=clusterCount c i := rfl

lemma labelCount_pos_iff {r : ℕ} (c : Fin r → ℕ) (x : ℕ) :
    0<labelCount c x ↔ x∈codeLabels c := by
  simp [labelCount,Finset.card_pos,codeLabels_mem,Finset.Nonempty]

lemma labelCount_succ {r : ℕ} (c : Fin (r+1) → ℕ) (x : ℕ) :
    labelCount c x=labelCount (restrictCode c) x+if c (Fin.last r)=x then 1 else 0 := by
  simp only [labelCount,Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  rfl

lemma codeLabels_succ {r : ℕ} (c : Fin (r+1) → ℕ) :
    codeLabels c=insert (c (Fin.last r)) (codeLabels (restrictCode c)) := by
  ext x
  simp only [codeLabels_mem,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    refine Fin.lastCases ?_ (fun j => ?_) i hi
    · exact fun h => Or.inl h.symm
    · exact fun h => Or.inr ⟨j,h⟩
  · rintro (h | ⟨i,hi⟩)
    · exact ⟨Fin.last r,h.symm⟩
    · exact ⟨i.castSucc,hi⟩

def blockFactor (a : ℝ) (n : ℕ) : ℝ :=
  ∏ j∈Finset.range (n-1),((j:ℝ)+1-a)

def tableFactor (a : ℝ) (k : ℕ) : ℝ :=
  ∏ j∈Finset.range (k-1),(a*((j:ℝ)+1))

@[simp] lemma blockFactor_one (a : ℝ) : blockFactor a 1=1 := by simp [blockFactor]
@[simp] lemma tableFactor_one (a : ℝ) : tableFactor a 1=1 := by simp [tableFactor]

lemma blockFactor_succ (a : ℝ) {n : ℕ} (hn : 0<n) :
    blockFactor a (n+1)=blockFactor a n*((n:ℝ)-a) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [blockFactor,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
  rw [Finset.prod_range_succ]
  push_cast
  rfl

lemma tableFactor_succ (a : ℝ) {n : ℕ} (hn : 0<n) :
    tableFactor a (n+1)=tableFactor a n*(a*(n:ℝ)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [tableFactor,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
  rw [Finset.prod_range_succ]
  push_cast
  rfl

def partitionNumerator {r : ℕ} (a : ℝ) (c : Fin r → ℕ) : ℝ :=
  tableFactor a (codeLabels c).card * ∏ x∈codeLabels c,blockFactor a (labelCount c x)

lemma codeLabels_nonempty {r : ℕ} (hr : 0<r) (c : Fin r → ℕ) :
    (codeLabels c).Nonempty := ⟨c ⟨0,hr⟩,(codeLabels_mem c _).mpr ⟨⟨0,hr⟩,rfl⟩⟩

lemma partitionNumerator_existing {r : ℕ} (a : ℝ) (c : Fin (r+1) → ℕ) (i : Fin r)
    (hi : restrictCode c i=c (Fin.last r)) :
    partitionNumerator a c=
      ((clusterCount (restrictCode c) i:ℝ)-a)*partitionNumerator a (restrictCode c) := by
  let x := c (Fin.last r)
  have hx : x∈codeLabels (restrictCode c) := (codeLabels_mem _ _).mpr ⟨i,hi⟩
  have hlabels : codeLabels c=codeLabels (restrictCode c) := by
    rw [codeLabels_succ,Finset.insert_eq_of_mem hx]
  have hcount : labelCount (restrictCode c) x=clusterCount (restrictCode c) i := by
    change labelCount (restrictCode c) (c (Fin.last r))=_
    rw [← hi]
    rfl
  have hprod : (∏ y∈codeLabels c,blockFactor a (labelCount c y))=
      (((clusterCount (restrictCode c) i:ℝ)-a))*
        ∏ y∈codeLabels (restrictCode c),blockFactor a (labelCount (restrictCode c) y) := by
    rw [hlabels,← Finset.mul_prod_erase _ _ hx,← Finset.mul_prod_erase _ _ hx]
    have he : (∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount c y))=
        ∏ y∈(codeLabels (restrictCode c)).erase x,blockFactor a (labelCount (restrictCode c) y) := by
      apply Finset.prod_congr rfl
      intro y hy
      rw [labelCount_succ,ite_eq_right (Ne.symm (Finset.mem_erase.mp hy).1),add_zero]
    rw [he,labelCount_succ,ite_eq_left rfl,hcount,blockFactor_succ a (clusterCount_pos _ i)]
    ring
  unfold partitionNumerator
  rw [hprod,hlabels]
  ring

lemma partitionNumerator_fresh {r : ℕ} (hr : 0<r) (a : ℝ) (c : Fin (r+1) → ℕ)
    (hi : ∀ i, restrictCode c i≠c (Fin.last r)) :
    partitionNumerator a c=a*((codeLabels (restrictCode c)).card:ℝ)*
      partitionNumerator a (restrictCode c) := by
  let x := c (Fin.last r)
  have hx : x∉codeLabels (restrictCode c) := by
    simpa only [codeLabels_mem,not_exists] using hi
  have hz : labelCount (restrictCode c) x=0 := by
    simpa only [← labelCount_pos_iff,not_lt,Nat.le_zero] using hx
  have hold : ∀ y∈codeLabels (restrictCode c),labelCount c y=labelCount (restrictCode c) y := by
    intro y hy
    have hyx : x≠y := fun h => hx (h ▸ hy)
    rw [labelCount_succ,ite_eq_right hyx,add_zero]
  unfold partitionNumerator
  rw [codeLabels_succ,Finset.card_insert_of_notMem hx,
    tableFactor_succ a (Finset.card_pos.mpr (codeLabels_nonempty hr _)),Finset.prod_insert hx]
  have hn : labelCount c x=1 := by rw [labelCount_succ,hz,ite_eq_left rfl,zero_add]
  rw [hn,blockFactor_one,one_mul]
  have he := Finset.prod_congr (s₁:=codeLabels (restrictCode c)) (s₂:=codeLabels (restrictCode c))
    rfl (fun y hy => congrArg (blockFactor a) (hold y hy))
  rw [he]
  ring

lemma ClusterReps.card_codeLabels {r : ℕ} {c : Fin r → ℕ} {S : Finset (Fin r)}
    (hS : ClusterReps c S) : S.card=(codeLabels c).card := by
  have he : S.image c=codeLabels c := by
    ext x
    simp only [Finset.mem_image,codeLabels_mem]
    constructor
    · rintro ⟨i,_,hi⟩; exact ⟨i,hi⟩
    · rintro ⟨i,rfl⟩
      exact hS.2 i
  rw [← he,Finset.card_image_of_injOn hS.1]

lemma partitionNumerator_one (a : ℝ) (c : Fin 1 → ℕ) : partitionNumerator a c=1 := by
  have hc : codeLabels c={c 0} := by
    ext x
    simp only [codeLabels_mem,Finset.mem_singleton]
    exact ⟨fun ⟨i,hi⟩ => by fin_cases i; exact hi.symm,fun h => ⟨0,h.symm⟩⟩
  have hn : labelCount c (c 0)=1 := by simp [labelCount,Finset.filter_singleton]
  simp [partitionNumerator,hc,hn]

 

theorem GG_partition_EPPF {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) {r : ℕ} (hr : 0<r) (c : Fin r → ℕ) :
    ((r-1).factorial:ℝ)*(μ:Measure OverlapArray).real (partitionEvent c q)=
      partitionNumerator (overlapDiscount μ q) c := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=0
    · subst r
      rw [partition_one_real hG c hq,partitionNumerator_one]
      norm_num
    have hr' : 0<r := Nat.pos_of_ne_zero hr0
    have hold := ih hr' (restrictCode c)
    have hf : (r.factorial:ℝ)=(r:ℝ)*((r-1).factorial:ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred hr0).symm
    simp only [Nat.add_sub_cancel] at *
    by_cases hc : ∃ i,restrictCode c i=c (Fin.last r)
    · obtain ⟨i,hi⟩ := hc
      rw [partitionNumerator_existing _ c i hi,hf]
      have he := GG_partition_existing hG hgg hu c hq i hi
      linear_combination ((r-1).factorial:ℝ)*he+
        ((clusterCount (restrictCode c) i:ℝ)-overlapDiscount μ q)*hold
    · have hc' : ∀ i,restrictCode c i≠c (Fin.last r) := not_exists.mp hc
      obtain ⟨S,hS⟩ := exists_clusterReps (restrictCode c)
      rw [partitionNumerator_fresh hr' _ c hc',hf]
      have he := GG_partition_fresh hG hgg hu c hq hS hc'
      rw [hS.card_codeLabels] at he
      linear_combination ((r-1).factorial:ℝ)*he+
        (overlapDiscount μ q*((codeLabels (restrictCode c)).card:ℝ))*hold

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def fallingCoeff (a : ℝ) (n : ℕ) : ℝ := ∏ j∈Finset.range n,(a-(j:ℝ))

@[simp] lemma fallingCoeff_zero (a : ℝ) : fallingCoeff a 0=1 := by simp [fallingCoeff]
lemma fallingCoeff_succ (a : ℝ) (n : ℕ) :
    fallingCoeff a (n+1)=fallingCoeff a n*(a-n) := by simp [fallingCoeff,Finset.prod_range_succ]

lemma iteratedDeriv_affine_rpow (a x : ℝ) (n : ℕ) {z : ℝ} (hz : 0<1-z*x) :
    iteratedDeriv n (fun z : ℝ => (1-z*x)^a) z=
      (-x)^n*fallingCoeff a n*(1-z*x)^(a-n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun z : ℝ => (1-z*x)^a) =ᶠ[𝓝 z]
        (fun w => (-x)^n*fallingCoeff a n*(1-w*x)^(a-n)) := by
      filter_upwards [(show Continuous (fun w : ℝ => 1-w*x) by fun_prop).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hz)] with w hw
      exact ih hw
    rw [he.deriv_eq]
    have hlin : HasDerivAt (fun w : ℝ => 1-w*x) (-x) z := by
      simpa using (((hasDerivAt_id z).mul_const x).const_sub 1)
    have hd := (hlin.rpow_const (p:=a-n) (Or.inl (ne_of_gt hz))).const_mul ((-x)^n*fallingCoeff a n)
    rw [hd.deriv,fallingCoeff_succ,pow_succ]
    have hn : a-(n+1:ℕ)=a-n-1 := by push_cast; ring
    rw [hn]
    ring

lemma iteratedDeriv_affine_rpow_zero (a x : ℝ) (n : ℕ) :
    iteratedDeriv n (fun z : ℝ => (1-z*x)^a) 0=(-x)^n*fallingCoeff a n := by
  simpa using iteratedDeriv_affine_rpow a x n (z:=0) (by norm_num)

lemma fallingCoeff_blockFactor (a : ℝ) {n : ℕ} (hn : 0<n) :
    (-1:ℝ)^n*fallingCoeff a n= -a*blockFactor a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n=0
    · subst n; simp [fallingCoeff_succ]
    have hn' : 0<n := Nat.pos_of_ne_zero h
    rw [pow_succ,fallingCoeff_succ,blockFactor_succ a hn']
    have he := ih hn'
    linear_combination -(a-n)*he

lemma iteratedDeriv_affine_rpow_zero_pos (a x : ℝ) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z : ℝ => (1-z*x)^a) 0= -a*blockFactor a n*x^n := by
  rw [iteratedDeriv_affine_rpow_zero,neg_eq_neg_one_mul,mul_pow]
  calc
    (-1:ℝ)^n*x^n*fallingCoeff a n=((-1:ℝ)^n*fallingCoeff a n)*x^n := by ring
    _ = _ := by rw [fallingCoeff_blockFactor a hn]

variable {ι : Type*} [Fintype ι]

def finiteMarkTransform (a : ℝ) (w x : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i,w i*(1-z*x i)^a

def finiteMarkMoment (w x : ι → ℝ) (n : ℕ) : ℝ := ∑ i,w i*x i^n

lemma contDiffAt_mark (a : ℝ) (w x : ι → ℝ) (n : ℕ∞ω) :
    ContDiffAt ℝ n (finiteMarkTransform a w x) 0 := by
  apply ContDiffAt.sum
  intro i _
  apply contDiffAt_const.mul
  apply ContDiffAt.rpow_const_of_ne
  · fun_prop
  · simp

lemma finiteMarkTransform_zero (a : ℝ) (w x : ι → ℝ) (hw : ∑ i,w i=1) :
    finiteMarkTransform a w x 0=1 := by simpa [finiteMarkTransform] using hw

lemma iteratedDeriv_mark (a : ℝ) (w x : ι → ℝ) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (finiteMarkTransform a w x) 0=
      -a*blockFactor a n*finiteMarkMoment w x n := by
  unfold finiteMarkTransform finiteMarkMoment
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field,iteratedDeriv_affine_rpow_zero_pos a _ hn,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact contDiffAt_const.mul ((show ContDiffAt ℝ n (fun z : ℝ => (1-z*x i)^a) 0 from
      (by
        apply ContDiffAt.rpow_const_of_ne
        · fun_prop
        · simp)))

end SKCavity

end

end OAI
