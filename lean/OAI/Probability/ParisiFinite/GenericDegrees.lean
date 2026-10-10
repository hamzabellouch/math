import Mathlib
import OAI.Probability.ParisiFinite.MixedReplicaIdentity

namespace OAI

/-! Generic Degrees. -/

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def genericDegrees (n : ℕ) : Fin (powerCutoff n+1) → ℕ := Fin.val

def genericMixedAmplitude (n : ℕ) (β : ℝ) : Fin (powerCutoff n+1) → ℝ :=
  if hn : 0<n then (exists_mixed_root_amplitude hn (genericDegrees n) β).choose else fun _ => 0

lemma genericMixedAmplitude_mem {n : ℕ} (hn : 0<n) (β : ℝ) (k : Fin (powerCutoff n+1)) :
    genericMixedAmplitude n β k∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3) := by
  rw [genericMixedAmplitude, dite_eq_left hn]
  exact (exists_mixed_root_amplitude hn (genericDegrees n) β).choose_spec.1 k

 
def genericMixedCoeff (n : ℕ) (β : ℝ) :=
  mixedCoeff n (genericDegrees n) β (genericMixedAmplitude n β)

 
def overlapGGDefect {n r : ℕ} {κ : Type*} [Fintype κ] (A : Configuration n → κ → ℝ)
    (p : ℕ) (i : Fin r) (f : (Fin r → Configuration n) → ℝ) : ℝ :=
  (r:ℝ)*averagedReplica A
      (fun τ : Fin (r+1) → Configuration n => f (fun l => τ l.castSucc)*
        (overlap (τ i.castSucc) (τ (Fin.last r)))^p)-
    averagedReplica A f*averagedReplica A
        (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^p)-
    averagedReplica A (fun σ => f σ*∑ l∈Finset.univ.erase i, (overlap (σ i) (σ l))^p)

lemma genericMixed_defect_le {n r : ℕ} (hn : 0<n) (β : ℝ) {p : ℕ} (hp : p ≤ powerCutoff n)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ) (hf : ∀ σ, |f σ| ≤ 1) :
    |overlapGGDefect (genericMixedCoeff n β) p i f| ≤ (82+8*|β|)/allPowerRoot n^2 := by
  let k : Fin (powerCutoff n+1) := ⟨p, Nat.lt_succ_of_le hp⟩
  have h := (exists_mixed_root_amplitude hn (genericDegrees n) β).choose_spec.2 k r i f hf
  have he : genericMixedAmplitude n β=(exists_mixed_root_amplitude hn (genericDegrees n) β).choose := by
    rw [genericMixedAmplitude, dite_eq_left hn]
  rw [← he] at h
  change |overlapGGDefect (genericMixedCoeff n β) p i f| ≤ _ at h
  exact h.trans (allPower_GG_rate hn β)

 

theorem tendsto_genericMixed_GG_defect (p : ℕ) (β : ℝ) (r : ℕ → ℕ)
    (i : ∀ n, Fin (r n)) (f : ∀ n, (Fin (r n) → Configuration n) → ℝ)
    (hf : ∀ n σ, |f n σ| ≤ 1) :
    Tendsto (fun n => overlapGGDefect (genericMixedCoeff n β) p (i n) (f n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  refine squeeze_zero' (g:=fun n => (82+8*|β|)/allPowerRoot n^2) (Eventually.of_forall fun n => abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0, tendsto_powerCutoff.eventually (eventually_ge_atTop p)] with n hn hp
    exact genericMixed_defect_le hn β hp (i n) (f n) (hf n)
  · have hr : Tendsto (fun n => (allPowerRoot n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_allPowerRoot
    simpa only [zero_pow (by decide : 2≠0), mul_zero, inv_pow, div_eq_mul_inv] using (hr.pow 2).const_mul (82+8*|β|)

lemma tendsto_genericMixed_variance_density (β : ℝ) :
    Tendsto (fun n => (∑ k, (genericMixedAmplitude n β k)^2)/(n:ℝ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => (allPowerRoot n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_allPowerRoot
  have hlim : Tendsto (fun n => 8/(allPowerRoot n^7)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 7≠0), mul_zero, inv_pow, div_eq_mul_inv] using (hr.pow 7).const_mul 8
  refine squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg n))) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact allPower_amplitude_variance_density hn _ (genericMixedAmplitude_mem hn β)

 

theorem tendsto_genericMixed_pressureDensity_error (β : ℝ) :
    Tendsto (fun n => (expected (genericMixedCoeff n β)-
      expected (fun s e => β*skCoeff n s e))/(n:ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  have hlim : Tendsto (fun n => Real.pi*((∑ k, (genericMixedAmplitude n β k)^2)/(n:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_genericMixed_variance_density β).const_mul Real.pi
  refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [abs_div]; rw [abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
  have h := div_le_div_of_nonneg_right (mixed_pressure_error hn (genericDegrees n) β (genericMixedAmplitude n β))
    (Nat.cast_nonneg n)
  simpa only [genericMixedCoeff, mul_div_assoc] using h

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

lemma replicaMean_prefix {r s : ℕ} (h : r ≤ s) (x : ι → ℝ) (f : (Fin r → ι) → ℝ) :
    replicaMean x (fun σ : Fin s → ι => f (fun i => σ (Fin.castLE h i)))=replicaMean x f := by
  induction s, h using Nat.le_induction with
  | base => simp
  | succ s h ih =>
    have he : (fun σ : Fin (s+1) → ι => f (fun i => σ (Fin.castLE (Nat.le_succ_of_le h) i)))=
        fun σ => (fun τ : Fin s → ι => f (fun i => τ (Fin.castLE h i))) (fun l => σ l.castSucc) := rfl
    rw [he]
    exact (replicaMean_marginal x (fun τ : Fin s → ι => f (fun i => τ (Fin.castLE h i)))).trans ih

lemma averagedReplica_prefix {r s : ℕ} (h : r ≤ s) (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) :
    averagedReplica A (fun σ : Fin s → ι => f (fun i => σ (Fin.castLE h i)))=averagedReplica A f := by
  simp only [averagedReplica, replicaMean_prefix h]

 
def fieldReplicaMass {r : ℕ} (A : ι → κ → ℝ) (σ : Fin r → ι) : ℝ :=
  ∫ z, replicaWeight (field A z) σ ∂gaussianLaw κ

lemma fieldReplicaMass_nonneg {r : ℕ} (A : ι → κ → ℝ) (σ : Fin r → ι) :
    0 ≤ fieldReplicaMass A σ := integral_nonneg fun _ => replicaWeight_nonneg _ _

lemma sum_fieldReplicaMass (r : ℕ) (A : ι → κ → ℝ) :
    (∑ σ : Fin r → ι, fieldReplicaMass A σ)=1 := by
  unfold fieldReplicaMass
  rw [← integral_finsetSum _ (fun σ _ => integrable_field_replicaWeight A σ)]
  simp only [sum_replicaWeight]
  simp

def fieldOverlapLaw {n t : ℕ} (A : Configuration n → κ → ℝ) : ProbabilityMeasure OverlapArray :=
  finiteProbability (fun σ : Fin (t+1) → Configuration n => fieldReplicaMass A σ)
    (fieldReplicaMass_nonneg A) (sum_fieldReplicaMass (t+1) A) configurationOverlap

lemma integral_fieldOverlapLaw {n t : ℕ} (A : Configuration n → κ → ℝ) (f : OverlapArray → ℝ) :
    (∫ R, f R ∂(fieldOverlapLaw (t:=t) A : Measure _))=
      averagedReplica A (fun σ : Fin (t+1) → Configuration n => f (configurationOverlap σ)) := by
  rw [fieldOverlapLaw, integral_finiteProbability]
  unfold averagedReplica replicaMean
  rw [integral_finsetSum _ (fun σ _ => (integrable_field_replicaWeight A σ).mul_const _)]
  simp only [integral_mul_const, fieldReplicaMass]

abbrev OverlapBlock (r : ℕ) := Fin r → Fin r → OverlapEntry

def blockOfArray (r : ℕ) (R : OverlapArray) : OverlapBlock r := fun i j => R i j

def blockOfReplicas {n r : ℕ} (σ : Fin r → Configuration n) : OverlapBlock r :=
  fun i j => ⟨overlap (σ i) (σ j), abs_le.mp (abs_overlap_le_one _ _)⟩

lemma continuous_blockOfArray (r : ℕ) : Continuous (blockOfArray r) := by
  unfold blockOfArray
  fun_prop

lemma blockOfArray_configurationOverlap {n r t : ℕ} (h : r ≤ t+1)
    (σ : Fin (t+1) → Configuration n) :
    blockOfArray r (configurationOverlap σ)=blockOfReplicas (fun i => σ (Fin.castLE h i)) := by
  funext i j
  apply Subtype.ext
  change overlap (extendReplicas σ i) (extendReplicas σ j)=_
  rw [show extendReplicas σ i=σ (Fin.castLE h i) from extendReplicas_eq σ (Fin.castLE h i),
    show extendReplicas σ j=σ (Fin.castLE h j) from extendReplicas_eq σ (Fin.castLE h j)]
  rfl

lemma integral_fieldOverlapLaw_block {n r t : ℕ} (h : r ≤ t+1)
    (A : Configuration n → κ → ℝ) (f : OverlapBlock r → ℝ) :
    (∫ R, f (blockOfArray r R) ∂(fieldOverlapLaw (t:=t) A : Measure _))=
      averagedReplica A (fun σ : Fin r → Configuration n => f (blockOfReplicas σ)) := by
  rw [integral_fieldOverlapLaw]
  simp_rw [blockOfArray_configurationOverlap h]
  exact averagedReplica_prefix h A (fun σ => f (blockOfReplicas σ))

 

def genericOverlapLaw (n : ℕ) (β : ℝ) : ProbabilityMeasure OverlapArray :=
  fieldOverlapLaw (t:=n) (genericMixedCoeff n β)

lemma genericOverlapLaw_Gram {n : ℕ} (hn : 0<n) (β : ℝ) :
    (genericOverlapLaw n β : Measure _) GramArrays=1 :=
  finiteProbability_set_of_forall _ (fieldReplicaMass_nonneg _) (sum_fieldReplicaMass (n+1) _) _ (configurationOverlap_mem_Gram hn)

lemma genericOverlap_limit_Gram (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ)) :
    (μ : Measure _) GramArrays=1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_GramArrays
  have he : ∀ᶠ k in atTop, (genericOverlapLaw (φ k) β : Measure _) GramArrays=(1:ℝ≥0∞) :=
    (hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)).mono (fun _ hk => genericOverlapLaw_Gram hk β)
  rw [limsup_congr he, limsup_const] at h
  exact le_antisymm prob_le_one h

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

def arrayGGDefect (μ : ProbabilityMeasure OverlapArray) (r p : ℕ) (i : Fin r)
    (f : OverlapBlock r → ℝ) : ℝ :=
  (r:ℝ)*(∫ R, f (blockOfArray r R)*(R i r : ℝ)^p ∂(μ : Measure OverlapArray)) -
    (∫ R, f (blockOfArray r R) ∂(μ : Measure OverlapArray)) *
      (∫ R, (R 0 1 : ℝ)^p ∂(μ : Measure OverlapArray)) -
    (∫ R, f (blockOfArray r R)*∑ l∈Finset.univ.erase i, (R i l : ℝ)^p ∂(μ : Measure OverlapArray))

lemma continuous_arrayGGDefect (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r, ℝ)) :
    Continuous (fun μ => arrayGGDefect μ r p i f) := by
  let f₁ : C(OverlapArray, ℝ) := ⟨fun R => f (blockOfArray r R)*(R i r : ℝ)^p, by unfold blockOfArray; fun_prop⟩
  let f₂ : C(OverlapArray, ℝ) := ⟨fun R => f (blockOfArray r R), by unfold blockOfArray; fun_prop⟩
  let f₃ : C(OverlapArray, ℝ) := ⟨fun R => (R 0 1 : ℝ)^p, by fun_prop⟩
  let f₄ : C(OverlapArray, ℝ) := ⟨fun R => f (blockOfArray r R)*∑ l∈Finset.univ.erase i, (R i l : ℝ)^p, by unfold blockOfArray; fun_prop⟩
  exact ((ProbabilityMeasure.continuous_integral_continuousMap f₁).const_mul r).sub
    ((ProbabilityMeasure.continuous_integral_continuousMap f₂).mul
      (ProbabilityMeasure.continuous_integral_continuousMap f₃)) |>.sub
        (ProbabilityMeasure.continuous_integral_continuousMap f₄)

lemma arrayGGDefect_fieldOverlapLaw {n t r : ℕ} (hr : r+1 ≤ t+1) (h₂ : 2 ≤ t+1)
    {κ : Type*} [Fintype κ] (A : Configuration n → κ → ℝ)
    (p : ℕ) (i : Fin r) (f : OverlapBlock r → ℝ) :
    arrayGGDefect (fieldOverlapLaw (t:=t) A) r p i f=
      overlapGGDefect A p i (fun σ => f (blockOfReplicas σ)) := by
  have h₁ := integral_fieldOverlapLaw_block hr A
    (fun T : OverlapBlock (r+1) => f (fun a b => T a.castSucc b.castSucc)*(T i.castSucc (Fin.last r) : ℝ)^p)
  have h₂' := integral_fieldOverlapLaw_block (Nat.le_trans (Nat.le_succ r) hr) A f
  have h₃ := integral_fieldOverlapLaw_block h₂ A (fun T : OverlapBlock 2 => (T 0 1 : ℝ)^p)
  have h₄ := integral_fieldOverlapLaw_block (Nat.le_trans (Nat.le_succ r) hr) A
    (fun T : OverlapBlock r => f T*∑ l∈Finset.univ.erase i, (T i l : ℝ)^p)
  change (∫ R, f (blockOfArray r R)*(R i r : ℝ)^p ∂(fieldOverlapLaw (t:=t) A : Measure OverlapArray)) =
    averagedReplica A (fun σ : Fin (r+1) → Configuration n =>
      f (blockOfReplicas (fun l => σ l.castSucc))*(overlap (σ i.castSucc) (σ (Fin.last r)))^p) at h₁
  change (∫ R, (R 0 1 : ℝ)^p ∂(fieldOverlapLaw (t:=t) A : Measure OverlapArray)) =
    averagedReplica A (fun σ : Fin 2 → Configuration n => (overlap (σ 0) (σ 1))^p) at h₃
  change (∫ R, f (blockOfArray r R)*∑ l∈Finset.univ.erase i, (R i l : ℝ)^p
      ∂(fieldOverlapLaw (t:=t) A : Measure OverlapArray)) =
    averagedReplica A (fun σ : Fin r → Configuration n =>
      f (blockOfReplicas σ)*∑ l∈Finset.univ.erase i, (overlap (σ i) (σ l))^p) at h₄
  unfold arrayGGDefect overlapGGDefect
  rw [h₁, h₂', h₃, h₄]

 

theorem genericOverlap_limit_GG (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r, ℝ)) (hf : ∀ R, |f R| ≤ 1) :
    arrayGGDefect μ r p i f=0 := by
  have hz := (tendsto_genericMixed_GG_defect p β (fun _ => r) (fun _ => i)
    (fun _ σ => f (blockOfReplicas σ)) (fun _ σ => hf _)).comp hφ.tendsto_atTop
  have he : ∀ᶠ k in atTop,
      overlapGGDefect (genericMixedCoeff (φ k) β) p i (fun σ => f (blockOfReplicas σ))=
        arrayGGDefect (genericOverlapLaw (φ k) β) r p i f := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (max r 1))] with k hk
    exact (arrayGGDefect_fieldOverlapLaw (by omega) (by omega) _ p i f).symm
  have hz' := hz.congr' he
  exact tendsto_nhds_unique ((continuous_arrayGGDefect r p i f).tendsto μ |>.comp hμ) hz'

 

theorem exists_generic_GG_Gram_limit (β : ℝ) :
    ∃ μ : ProbabilityMeasure OverlapArray,
      (μ : Measure OverlapArray) GramArrays=1 ∧
      (∀ (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r, ℝ)),
        (∀ R, |f R| ≤ 1) → arrayGGDefect μ r p i f=0) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ) := by
  obtain ⟨μ,φ,hφ,hμ⟩ := CompactSpace.tendsto_subseq (fun n => genericOverlapLaw n β)
  exact ⟨μ,genericOverlap_limit_Gram β hφ hμ,fun r p i f hf => genericOverlap_limit_GG β hφ hμ r p i f hf,φ,hφ,hμ⟩

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma integrable_continuousMap {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℝ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)

 
def continuousIntegral {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : ProbabilityMeasure X) : C(X,ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (integrable_continuousMap _ f) (integrable_continuousMap _ g)
      map_smul' := fun c f => integral_smul c f } 1 (by
        intro f
        simpa using norm_integral_le_of_norm_le_const (μ:=(μ:Measure X)) (ae_of_all _ f.norm_coe_le_norm))

 
def overlapIntegral (μ : ProbabilityMeasure OverlapArray) (f : C(OverlapArray,ℝ))
    (i j : ℕ) : C(OverlapEntry,ℝ) →L[ℝ] ℝ :=
  (continuousIntegral μ).comp ((ContinuousLinearMap.mul ℝ C(OverlapArray,ℝ) f).comp
    (ContinuousMap.compCLM ℝ ℝ ⟨fun R => R i j, by fun_prop⟩))

@[simp] lemma overlapIntegral_apply (μ : ProbabilityMeasure OverlapArray)
    (f : C(OverlapArray,ℝ)) (i j : ℕ) (ψ : C(OverlapEntry,ℝ)) :
    overlapIntegral μ f i j ψ=∫ R, f R*ψ (R i j) ∂(μ : Measure OverlapArray) := rfl

 

def continuousGG (μ : ProbabilityMeasure OverlapArray) (r : ℕ) (i : Fin r)
    (f : C(OverlapBlock r,ℝ)) : C(OverlapEntry,ℝ) →L[ℝ] ℝ :=
  let F : C(OverlapArray,ℝ) := f.comp ⟨blockOfArray r, continuous_blockOfArray r⟩
  (r:ℝ) • overlapIntegral μ F i r - continuousIntegral μ F • overlapIntegral μ 1 0 1 -
    ∑ l∈Finset.univ.erase i, overlapIntegral μ F i l

def overlapPower (p : ℕ) : C(OverlapEntry,ℝ) := ⟨fun x => (x:ℝ)^p, by fun_prop⟩

lemma continuousGG_power (μ : ProbabilityMeasure OverlapArray) (r p : ℕ) (i : Fin r)
    (f : C(OverlapBlock r,ℝ)) : continuousGG μ r i f (overlapPower p)=arrayGGDefect μ r p i f := by
  unfold continuousGG arrayGGDefect
  simp only [sub_apply, smul_apply,
    sum_apply, overlapIntegral_apply, ContinuousMap.one_apply,
    one_mul, smul_eq_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  exact (integral_finsetSum (Finset.univ.erase i) (fun (l : Fin r) _ => integrable_continuousMap (μ:Measure OverlapArray)
    ⟨fun R => f (blockOfArray r R)*(R i l : ℝ)^p, by unfold blockOfArray; fun_prop⟩)).symm

lemma arrayGGDefect_const_mul (μ : ProbabilityMeasure OverlapArray) (r p : ℕ) (i : Fin r)
    (f : OverlapBlock r → ℝ) (c : ℝ) :
    arrayGGDefect μ r p i (fun R => c*f R)=c*arrayGGDefect μ r p i f := by
  unfold arrayGGDefect
  simp only [mul_assoc, integral_const_mul]
  ring

lemma genericOverlap_limit_GG_unbounded (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r p : ℕ) (i : Fin r) (f : C(OverlapBlock r,ℝ)) : arrayGGDefect μ r p i f=0 := by
  let M : ℝ := ‖f‖+1
  have hm : 0<M := by dsimp [M]; positivity
  have hf : ∀ R, |((M⁻¹) • f) R| ≤ 1 := by
    intro R
    change |M⁻¹*f R| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hm), ← div_eq_inv_mul]
    apply (div_le_one hm).mpr
    have := f.norm_coe_le_norm R
    simpa only [Real.norm_eq_abs] using this.trans (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1))
  have h := genericOverlap_limit_GG β hφ hμ r p i (M⁻¹ • f) hf
  change arrayGGDefect μ r p i (fun R => M⁻¹*f R)=0 at h
  rw [arrayGGDefect_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hm.ne')

 
theorem genericOverlap_limit_continuousGG (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r : ℕ) (i : Fin r) (f : C(OverlapBlock r,ℝ)) (ψ : C(OverlapEntry,ℝ)) :
    continuousGG μ r i f ψ=0 := by
  let L := continuousGG μ r i f
  have hp (p : ℕ) : L (overlapPower p)=0 := by
    rw [continuousGG_power]
    exact genericOverlap_limit_GG_unbounded β hφ hμ r p i f
  have hpoly (p : Polynomial ℝ) : L (p.toContinuousMapOn (Set.Icc (-1:ℝ) 1))=0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have he : (p+q).toContinuousMapOn (Set.Icc (-1:ℝ) 1)=p.toContinuousMapOn _+q.toContinuousMapOn _ := by
        ext x; simp [Polynomial.toContinuousMapOn]
      rw [he, map_add, hp, hq, add_zero]
    | monomial p a =>
      have he : (Polynomial.monomial p a).toContinuousMapOn (Set.Icc (-1:ℝ) 1)=a • overlapPower p := by
        ext x; simp [Polynomial.toContinuousMapOn, overlapPower]
      rw [he, map_smul, hp, smul_zero]
  have hs : (polynomialFunctions (Set.Icc (-1:ℝ) 1) : Set C(OverlapEntry,ℝ)) ⊆ {g | L g=0} := by
    intro g hg
    rw [polynomialFunctions_coe] at hg
    rcases hg with ⟨p,rfl⟩
    exact hpoly p
  have hc := closure_minimal hs (isClosed_eq L.continuous continuous_const)
  exact hc (continuousMap_mem_polynomialFunctions_closure (-1) 1 ψ)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def blockOverlapMap (r : ℕ) (i j : ℕ) (R : OverlapArray) : OverlapBlock r × OverlapEntry :=
  (blockOfArray r R, R i j)

lemma continuous_blockOverlapMap (r : ℕ) (i j : ℕ) : Continuous (blockOverlapMap r i j) :=
  (continuous_blockOfArray r).prodMk (by fun_prop)

def jointOverlapLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) (i j : ℕ) :
    Measure (OverlapBlock r × OverlapEntry) := (μ : Measure OverlapArray).map (blockOverlapMap r i j)

instance instIsFiniteJointOverlapLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) (i j : ℕ) :
    IsFiniteMeasure (jointOverlapLaw μ r i j) := by unfold jointOverlapLaw; infer_instance

lemma integral_jointOverlapLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) (i j : ℕ)
    (f : C(OverlapBlock r,ℝ)) (ψ : C(OverlapEntry,ℝ)) :
    (∫ z, f z.1*ψ z.2 ∂jointOverlapLaw μ r i j)=overlapIntegral μ
      (f.comp ⟨blockOfArray r,continuous_blockOfArray r⟩) i j ψ := by
  rw [jointOverlapLaw, integral_map (continuous_blockOverlapMap r i j).measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : OverlapBlock r × OverlapEntry => f z.1*ψ z.2)
      ((μ:Measure _).map (blockOverlapMap r i j)) from (by fun_prop : Continuous _).aestronglyMeasurable)]
  rfl

def blockLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) : Measure (OverlapBlock r) :=
  (μ : Measure OverlapArray).map (blockOfArray r)

def entryLaw (μ : ProbabilityMeasure OverlapArray) (i j : ℕ) : Measure OverlapEntry :=
  (μ : Measure OverlapArray).map (fun R => R i j)

instance instIsFiniteBlockLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ) :
    IsFiniteMeasure (blockLaw μ r) := by unfold blockLaw; infer_instance
instance instIsFiniteEntryLaw (μ : ProbabilityMeasure OverlapArray) (i j : ℕ) :
    IsFiniteMeasure (entryLaw μ i j) := by unfold entryLaw; infer_instance

lemma integral_blockLaw (μ : ProbabilityMeasure OverlapArray) (r : ℕ)
    (f : C(OverlapBlock r,ℝ)) :
    (∫ z, f z ∂blockLaw μ r)=continuousIntegral μ (f.comp ⟨blockOfArray r,continuous_blockOfArray r⟩) := by
  rw [blockLaw, integral_map (continuous_blockOfArray r).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rfl

lemma integral_entryLaw (μ : ProbabilityMeasure OverlapArray) (i j : ℕ)
    (ψ : C(OverlapEntry,ℝ)) : (∫ z, ψ z ∂entryLaw μ i j)=overlapIntegral μ 1 i j ψ := by
  rw [entryLaw, integral_map (by fun_prop : Measurable (fun R : OverlapArray => R i j)).aemeasurable
    ψ.continuous.aestronglyMeasurable, overlapIntegral_apply]
  simp

 

theorem GG_measure_identity (μ : ProbabilityMeasure OverlapArray) (r : ℕ) (i : Fin r)
    (h : ∀ (f : C(OverlapBlock r,ℝ)) (ψ : C(OverlapEntry,ℝ)), continuousGG μ r i f ψ=0) :
    (r:ℝ≥0∞) • jointOverlapLaw μ r i r =
      (blockLaw μ r).prod (entryLaw μ 0 1)+∑ l∈Finset.univ.erase i, jointOverlapLaw μ r i l := by
  let : IsFiniteMeasure ((r:ℝ≥0∞) • jointOverlapLaw μ r i r) := Measure.smul_finite _ (by finiteness)
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f ψ
  let F : C(OverlapBlock r × OverlapEntry,ℝ) := ⟨fun z => f z.1*ψ z.2, by fun_prop⟩
  have hi (ν : Measure (OverlapBlock r × OverlapEntry)) [IsFiniteMeasure ν] :
      Integrable (fun z => f z.1*ψ z.2) ν := integrable_continuousMap ν F
  rw [integral_smul_measure, integral_add_measure (hi _) (hi _),
    integral_finsetSum_measure (fun l _ => hi _), integral_prod_mul]
  have hj (j : ℕ) := integral_jointOverlapLaw μ r i j f.toContinuousMap ψ.toContinuousMap
  change ∀ j, (∫ z, f z.1*ψ z.2 ∂jointOverlapLaw μ r i j)=_ at hj
  have hb := integral_blockLaw μ r f.toContinuousMap
  change (∫ z, f z ∂blockLaw μ r)=_ at hb
  have he := integral_entryLaw μ 0 1 ψ.toContinuousMap
  change (∫ z, ψ z ∂entryLaw μ 0 1)=_ at he
  simp_rw [hj, hb, he]
  have hz := h f.toContinuousMap ψ.toContinuousMap
  unfold continuousGG at hz
  simp only [sub_apply, smul_apply,
    sum_apply, smul_eq_mul] at hz
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
  linarith

 

theorem genericOverlap_limit_measureGG (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r : ℕ) (i : Fin r) :
    (r:ℝ≥0∞) • jointOverlapLaw μ r i r =
      (blockLaw μ r).prod (entryLaw μ 0 1)+∑ l∈Finset.univ.erase i, jointOverlapLaw μ r i l :=
  GG_measure_identity μ r i (genericOverlap_limit_continuousGG β hφ hμ r i)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Nonempty ι] in
lemma replicaWeight_perm {r : ℕ} (x : ι → ℝ) (e : Equiv.Perm (Fin r)) (σ : Fin r → ι) :
    replicaWeight x (fun i => σ (e i))=replicaWeight x σ :=
  Equiv.prod_comp e (fun i => weight x (σ i))

omit [Nonempty ι] in
lemma replicaMean_perm {r : ℕ} (x : ι → ℝ) (e : Equiv.Perm (Fin r)) (f : (Fin r → ι) → ℝ) :
    replicaMean x (fun σ => f (fun i => σ (e i)))=replicaMean x f := by
  let E : (Fin r → ι) ≃ (Fin r → ι) := Equiv.arrowCongr e.symm (Equiv.refl ι)
  have he (σ : Fin r → ι) : E σ=fun i => σ (e i) := rfl
  unfold replicaMean
  calc
    _ = ∑ σ, replicaWeight x (E σ)*f (E σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [he,replicaWeight_perm]
    _ = _ := E.sum_comp (fun σ => replicaWeight x σ*f σ)

lemma replicaMean_injection {r s : ℕ} (h : r ≤ s) (e : Fin r → Fin s) (he : Function.Injective e)
    (x : ι → ℝ) (f : (Fin r → ι) → ℝ) :
    replicaMean x (fun σ : Fin s → ι => f (fun i => σ (e i)))=replicaMean x f := by
  obtain ⟨q,hq⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE h) e (Fin.castLE_injective h) he
  have hh := replicaMean_perm x q (fun σ : Fin s → ι => f (fun i => σ (Fin.castLE h i)))
  simp only [hq] at hh
  exact hh.trans (replicaMean_prefix h x f)

lemma averagedReplica_injection {r s : ℕ} (h : r ≤ s) (e : Fin r → Fin s) (he : Function.Injective e)
    (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) :
    averagedReplica A (fun σ : Fin s → ι => f (fun i => σ (e i)))=averagedReplica A f := by
  simp only [averagedReplica, replicaMean_injection h e he]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def selectedBlock {r : ℕ} (e : Fin r → ℕ) (R : OverlapArray) : OverlapBlock r :=
  fun i j => R (e i) (e j)

lemma continuous_selectedBlock {r : ℕ} (e : Fin r → ℕ) : Continuous (selectedBlock e) := by
  unfold selectedBlock
  fun_prop

lemma integral_fieldOverlapLaw_selected {n t r : ℕ} (hr : r ≤ t+1)
    (e : Fin r → ℕ) (he : Function.Injective e) (ht : ∀ i, e i<t+1)
    {κ : Type*} [Fintype κ] (A : Configuration n → κ → ℝ) (f : OverlapBlock r → ℝ) :
    (∫ R, f (selectedBlock e R) ∂(fieldOverlapLaw (t:=t) A : Measure OverlapArray))=
      averagedReplica A (fun σ : Fin r → Configuration n => f (blockOfReplicas σ)) := by
  let e' : Fin r → Fin (t+1) := fun i => ⟨e i,ht i⟩
  have he' : Function.Injective e' := fun a b h => he (congrArg Fin.val h)
  rw [integral_fieldOverlapLaw]
  have hh (σ : Fin (t+1) → Configuration n) :
      selectedBlock e (configurationOverlap σ)=blockOfReplicas (fun i => σ (e' i)) := by
    funext i j
    apply Subtype.ext
    change overlap (extendReplicas σ (e' i)) (extendReplicas σ (e' j))=_
    simp only [extendReplicas_eq]
    rfl
  simp_rw [hh]
  exact averagedReplica_injection hr e' he' A (fun σ => f (blockOfReplicas σ))

lemma genericOverlap_limit_exchangeable_integral (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r : ℕ) (e : Fin r → ℕ) (he : Function.Injective e) (f : C(OverlapBlock r,ℝ)) :
    (∫ R, f (selectedBlock e R) ∂(μ : Measure OverlapArray))=
      ∫ R, f (blockOfArray r R) ∂(μ : Measure OverlapArray) := by
  let F : C(OverlapArray,ℝ) := f.comp ⟨selectedBlock e,continuous_selectedBlock e⟩
  let G : C(OverlapArray,ℝ) := f.comp ⟨blockOfArray r,continuous_blockOfArray r⟩
  have hF := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto μ |>.comp hμ
  have hG := (ProbabilityMeasure.continuous_integral_continuousMap G).tendsto μ |>.comp hμ
  have ha : ∀ᶠ k in atTop,
      (∫ R, F R ∂(genericOverlapLaw (φ k) β : Measure OverlapArray))=
        ∫ R, G R ∂(genericOverlapLaw (φ k) β : Measure OverlapArray) := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (max r (∑ i,e i)))] with k hk
    have hr : r ≤ φ k+1 := by omega
    have ht (i : Fin r) : e i<φ k+1 := by
      have h := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
      omega
    change (∫ R, f (selectedBlock e R) ∂(fieldOverlapLaw (t:=φ k) (genericMixedCoeff (φ k) β) : Measure _))=_
    rw [integral_fieldOverlapLaw_selected hr e he ht]
    exact (integral_fieldOverlapLaw_block hr _ f).symm
  exact tendsto_nhds_unique (hF.congr' ha) hG

 
theorem genericOverlap_limit_exchangeable (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ))
    (r : ℕ) (e : Fin r → ℕ) (he : Function.Injective e) :
    (μ : Measure OverlapArray).map (selectedBlock e)=blockLaw μ r := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_selectedBlock e).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    blockLaw, integral_map (continuous_blockOfArray r).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact genericOverlap_limit_exchangeable_integral β hφ hμ r e he f.toContinuousMap

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def GGIdentities (μ : ProbabilityMeasure OverlapArray) : Prop :=
  ∀ (r : ℕ) (i : Fin r), (r:ℝ≥0∞) • jointOverlapLaw μ r i r =
    (blockLaw μ r).prod (entryLaw μ 0 1)+∑ l∈Finset.univ.erase i, jointOverlapLaw μ r i l

theorem genericOverlap_limit_GGIdentities (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => genericOverlapLaw (φ k) β) atTop (𝓝 μ)) : GGIdentities μ :=
  genericOverlap_limit_measureGG β hφ hμ

lemma GG_event_identity {μ : ProbabilityMeasure OverlapArray} (h : GGIdentities μ)
    (r : ℕ) (i : Fin r) (B : Set (OverlapBlock r)) (A : Set OverlapEntry)
    (hB : MeasurableSet B) (hA : MeasurableSet A) :
    (r:ℝ)*(μ : Measure OverlapArray).real {R | blockOfArray r R∈B ∧ R i r∈A}=
      (μ : Measure OverlapArray).real ((blockOfArray r) ⁻¹' B)*(entryLaw μ 0 1).real A+
      ∑ l∈Finset.univ.erase i, (μ : Measure OverlapArray).real {R | blockOfArray r R∈B ∧ R i l∈A} := by
  have he := congrArg (fun ν : Measure (OverlapBlock r × OverlapEntry) => ν (B ×ˢ A)) (h r i)
  rw [Measure.smul_apply, Measure.add_apply, Measure.prod_prod,
    Measure.finsetSum_apply] at he
  simp only [smul_eq_mul] at he
  have hj (j : ℕ) : jointOverlapLaw μ r i j (B ×ˢ A)=
      (μ : Measure OverlapArray) {R | blockOfArray r R∈B ∧ R i j∈A} := by
    rw [jointOverlapLaw, Measure.map_apply (continuous_blockOverlapMap r i j).measurable (hB.prod hA)]
    rfl
  simp_rw [hj] at he
  rw [blockLaw, Measure.map_apply (continuous_blockOfArray r).measurable hB] at he
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_add (by finiteness) (by
      exact ENNReal.sum_ne_top.mpr (fun l hl => measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_sum (by intro l hl; finiteness)] at he'
  exact he'

lemma entryLaw_probability (μ : ProbabilityMeasure OverlapArray) (i j : ℕ) :
    IsProbabilityMeasure (entryLaw μ i j) := by
  unfold entryLaw
  infer_instance

end SKCavity

end

end OAI
