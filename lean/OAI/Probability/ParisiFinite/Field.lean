import Mathlib
import OAI.Probability.ParisiFinite.Sine

namespace OAI

/-! Field. -/

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
namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

def field (d : E) (g : E) : ℝ := ⟪d,g⟫

theorem memLp_field (d : E) : MemLp (field E d) 2 (stdGaussian E) := by
  exact (innerSL ℝ d).comp_memLp' IsGaussian.memLp_two_id

def vector (d : E) : Lp ℝ 2 (stdGaussian E) := (memLp_field E d).toLp (field E d)

theorem vector_ae (d : E) : (vector E d : E → ℝ)=ᵐ[stdGaussian E] field E d :=
  (memLp_field E d).coeFn_toLp

theorem field_covariance (d e : E) :
    (∫g, field E d g*field E e g ∂stdGaussian E)=⟪d,e⟫ := by
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id d e
  rw [covarianceBilin_stdGaussian] at h
  simpa only [field,id_eq,integral_id_stdGaussian,sub_zero,innerSL_apply_apply ℝ] using h.symm

theorem inner_vector (d e : E) : ⟪vector E d,vector E e⟫=⟪d,e⟫ := by
  rw [L2.inner_def,←field_covariance E d e]
  apply integral_congr_ae
  filter_upwards [vector_ae E d,vector_ae E e] with g hd he
  rw [hd,he]
  simp only [RCLike.inner_apply',starRingEnd_apply,star_trivial]

def linearMap : E →ₗ[ℝ] Lp ℝ 2 (stdGaussian E) where
  toFun := vector E
  map_add' d e := by
    apply Lp.ext
    filter_upwards [vector_ae E (d+e),vector_ae E d,vector_ae E e,
      Lp.coeFn_add (vector E d) (vector E e)] with g h1 h2 h3 h4
    rw [h1,h4]
    simp only [Pi.add_apply]
    rw [h2,h3]
    exact inner_add_left d e g
  map_smul' c d := by
    apply Lp.ext
    filter_upwards [vector_ae E (c • d),vector_ae E d,
      Lp.coeFn_smul c (vector E d)] with g h1 h2 h3
    simp only [RingHom.id_apply]
    rw [h1,h3]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [h2]
    exact real_inner_smul_left d g c

 

def aggregate : E →ₗᵢ[ℝ] Lp ℝ 2 (stdGaussian E) :=
  LinearMap.isometryOfInner (linearMap E) (inner_vector E)

@[simp] theorem aggregate_apply (d : E) : aggregate E d=vector E d := rfl

@[simp] theorem norm_aggregate_sub (d e : E) :
    ‖aggregate E d-aggregate E e‖=‖d-e‖ := by
  rw [←map_sub,(aggregate E).norm_map]

theorem aggregate_centered (d : E) : (∫g, aggregate E d g ∂stdGaussian E)=0 := by
  change (∫g, vector E d g ∂stdGaussian E)=0
  rw [integral_congr_ae (vector_ae E d)]
  exact integral_strongDual_stdGaussian (innerSL ℝ d)

 

theorem reflection : MeasurePreserving (fun g : E => -g) (stdGaussian E) (stdGaussian E) := by
  refine ⟨measurable_neg,?_⟩
  exact stdGaussian_map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)

theorem aggregate_odd (d : E) :
    ∀ᵐ g ∂stdGaussian E, aggregate E d (-g)= -aggregate E d g := by
  have ha := (reflection E).quasiMeasurePreserving.ae (vector_ae E d)
  filter_upwards [vector_ae E d,ha] with g h1 h2
  change vector E d (-g)= -vector E d g
  rw [h1,h2]
  exact inner_neg_right d g

 
theorem field_law (d : E) :
    (stdGaussian E).map (field E d)=gaussianReal 0 (‖d‖₊^2) := by
  change (stdGaussian E).map (innerSL ℝ d)=_
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  congr 1
  simp only [innerSL_apply_norm]
  apply NNReal.coe_injective
  simp only [Real.coe_toNNReal' , NNReal.coe_pow,coe_nnnorm,sup_eq_left.mpr (sq_nonneg ‖d‖)]

end ClassicalGaussian

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {κ : Type*} [Fintype κ] (cols : κ → V)

 
abbrev ColumnSpan := Submodule.span ℝ (Set.range cols)

instance span_finiteDimensional : FiniteDimensional ℝ (ColumnSpan cols) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range cols)

instance span_measurableSpace : MeasurableSpace (ColumnSpan cols) := borel (ColumnSpan cols)
instance span_borelSpace : BorelSpace (ColumnSpan cols) := ⟨rfl⟩

 
def column (k : κ) : ColumnSpan cols := ⟨cols k, Submodule.subset_span (Set.mem_range_self k)⟩

omit [Fintype κ] in
@[simp] theorem inner_column (j k : κ) : ⟪column cols j,column cols k⟫=⟪cols j,cols k⟫ := rfl
omit [Fintype κ] in
@[simp] theorem norm_column_sub (j k : κ) : ‖column cols j-column cols k‖=‖cols j-cols k‖ := rfl

 

def jointColumn (k : κ) : Lp ℝ 2 (stdGaussian (ColumnSpan cols)) :=
  aggregate (ColumnSpan cols) (column cols k)

theorem jointColumn_covariance (j k : κ) :
    (∫g, jointColumn cols j g*jointColumn cols k g ∂stdGaussian (ColumnSpan cols))=
      ⟪cols j,cols k⟫ := by
  rw [←inner_column cols j k,←field_covariance (ColumnSpan cols) (column cols j) (column cols k)]
  apply integral_congr_ae
  filter_upwards [vector_ae (ColumnSpan cols) (column cols j),
    vector_ae (ColumnSpan cols) (column cols k)] with g h1 h2
  change vector (ColumnSpan cols) (column cols j) g *
    vector (ColumnSpan cols) (column cols k) g = _
  rw [h1,h2]

theorem jointColumn_centered (k : κ) :
    (∫g, jointColumn cols k g ∂stdGaussian (ColumnSpan cols))=0 :=
  aggregate_centered (ColumnSpan cols) (column cols k)

theorem jointColumn_norm_sub (j k : κ) :
    ‖jointColumn cols j-jointColumn cols k‖=‖cols j-cols k‖ :=
  norm_aggregate_sub (ColumnSpan cols) (column cols j) (column cols k)

theorem jointColumn_odd (k : κ) :
    ∀ᵐ g ∂stdGaussian (ColumnSpan cols), jointColumn cols k (-g)= -jointColumn cols k g :=
  aggregate_odd (ColumnSpan cols) (column cols k)

end ClassicalGaussian

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

 

theorem projection_gaussian (i : E →ₗᵢ[ℝ] F) :
    (stdGaussian F).map (ContinuousLinearMap.adjoint i.toContinuousLinearMap)=stdGaussian E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.adjoint_inner_left]
  change charFun (stdGaussian F) (i t)=charFun (stdGaussian E) t
  simp only [charFun_stdGaussian,i.norm_map]

theorem projection_preserving (i : E →ₗᵢ[ℝ] F) :
    MeasurePreserving (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
      (stdGaussian F) (stdGaussian E) :=
  ⟨by fun_prop,projection_gaussian i⟩

 

theorem aggregate_pullback (i : E →ₗᵢ[ℝ] F) (d : E) :
    Lp.compMeasurePreserving (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
      (projection_preserving i) (aggregate E d)=aggregate F (i d) := by
  apply Lp.ext
  have h1 := (projection_preserving i).quasiMeasurePreserving.ae (vector_ae E d)
  filter_upwards [Lp.coeFn_compMeasurePreserving (aggregate E d) (projection_preserving i),
    h1,vector_ae F (i d)] with g h2 h3 h4
  change _=vector F (i d) g
  rw [h2,h4]
  change vector E d (ContinuousLinearMap.adjoint i.toContinuousLinearMap g)=_
  rw [h3]
  exact ContinuousLinearMap.adjoint_inner_right i.toContinuousLinearMap d g

end ClassicalGaussian

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory TrigLp
open scoped Topology
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {κ : Type*} [Fintype κ]

 

theorem exists_robust_gaussian_operation (cols : κ → E) (φ : (κ → ℝ) → ℝ)
    (hφ : MemLp φ 2 (inputLaw (stdGaussian E) (fun k => aggregate E (cols k))))
    (ho : ∀x, φ (-x)= -φ x) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀d : κ → E, (∀k, ‖d k-cols k‖<δ) →
        ‖polynomial (stdGaussian E) s b (fun k => aggregate E (d k))-
          (hφ.comp_measurePreserving (inputMap_preserving (stdGaussian E)
            (fun k => aggregate E (cols k)))).toLp
              (φ ∘ inputMap (stdGaussian E) (fun k => aggregate E (cols k)))‖<ε := by
  obtain ⟨s,b,δ,hδ,hd⟩ := exists_robust_odd_operation (stdGaussian E) (fun g => -g)
    (reflection E) (fun k => aggregate E (cols k)) (fun k => aggregate_odd E (cols k))
    φ hφ ho hε
  refine ⟨s,b,δ,hδ,?_⟩
  intro d hd'
  apply hd
  intro k
  simpa only [norm_aggregate_sub] using hd' k

 

theorem exists_robust_gaussian_angle (cols : κ → E) (φ : (κ → ℝ) → ℝ)
    (hφ : MemLp φ 2 (inputLaw (stdGaussian E) (fun k => aggregate E (cols k))))
    (ho : ∀x, φ (-x)= -φ x) (hb : ∀x, |φ x|≤1) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀d : κ → E, (∀k, ‖d k-cols k‖<δ) →
        ‖readout (stdGaussian E) s b (fun k => aggregate E (d k))-
          (hφ.comp_measurePreserving (inputMap_preserving (stdGaussian E)
            (fun k => aggregate E (cols k)))).toLp
              (φ ∘ inputMap (stdGaussian E) (fun k => aggregate E (cols k)))‖<ε := by
  obtain ⟨s,b,δ,hδ,hd⟩ := exists_robust_odd_readout (stdGaussian E) (fun g => -g)
    (reflection E) (fun k => aggregate E (cols k)) (fun k => aggregate_odd E (cols k))
    φ hφ ho hb hε
  refine ⟨s,b,δ,hδ,?_⟩
  intro d hd'
  apply hd
  intro k
  simpa only [norm_aggregate_sub] using hd' k

end ClassicalGaussian

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

theorem covariance_field (d e : E) :
    cov[field E d,field E e;stdGaussian E]=⟪d,e⟫ := by
  rw [covariance_eq_sub (memLp_field E d) (memLp_field E e)]
  have hd : (∫g,field E d g ∂stdGaussian E)=0 :=
    integral_strongDual_stdGaussian (innerSL ℝ d)
  have he : (∫g,field E e g ∂stdGaussian E)=0 :=
    integral_strongDual_stdGaussian (innerSL ℝ e)
  rw [hd,he,mul_zero,sub_zero]
  exact field_covariance E d e

 

theorem joint_gaussian {κ : Type*} [Fintype κ] (cols : κ → E) :
    HasGaussianLaw (fun g k => field E (cols k) g) (stdGaussian E) := by
  exact HasGaussianLaw.map_of_measurable
    (ContinuousLinearMap.pi (fun k => innerSL ℝ (cols k)))
    IsGaussian.hasGaussianLaw_id (by fun_prop)

 
theorem fields_independent {κ : Type*} [Fintype κ] (cols : κ → E)
    (h : ∀j k, j≠k → ⟪cols j,cols k⟫=0) :
    iIndepFun (fun k => field E (cols k)) (stdGaussian E) := by
  apply (joint_gaussian E cols).iIndepFun_of_covariance_eq_zero
  intro j k hjk
  rw [covariance_field]
  exact h j k hjk

 

theorem orthogonal_families_independent {κ ι : Type*} [Fintype κ] [Fintype ι]
    (d : κ → E) (e : ι → E) (h : ∀j k, ⟪d j,e k⟫=0) :
    IndepFun (fun g j => field E (d j) g) (fun g k => field E (e k) g)
      (stdGaussian E) := by
  have hg : HasGaussianLaw (fun g => ((fun j => field E (d j) g),
      (fun k => field E (e k) g))) (stdGaussian E) := by
    exact HasGaussianLaw.map_of_measurable
      ((ContinuousLinearMap.pi (fun j => innerSL ℝ (d j))).prod
        (ContinuousLinearMap.pi (fun k => innerSL ℝ (e k))))
      IsGaussian.hasGaussianLaw_id (by fun_prop)
  apply hg.indepFun_of_covariance_eval
  intro j k
  rw [covariance_field]
  exact h j k

end ClassicalGaussian

namespace TrigLp
open MeasureTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable (μ : Measure Ω) (ν : Measure Ω') (X : Ω → Ω')
variable (hX : MeasurePreserving X μ ν)
variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
 

theorem sine_pullback (f : Lp ℝ 2 ν) :
    Lp.compMeasurePreservingₗ ℝ X hX (sine ν f)=
      sine μ (Lp.compMeasurePreservingₗ ℝ X hX f) := by
  apply Lp.ext
  have hf := hX.quasiMeasurePreserving.ae (sine_ae ν f)
  filter_upwards [Lp.coeFn_compMeasurePreserving (sine ν f) hX,hf,
    sine_ae μ (Lp.compMeasurePreservingₗ ℝ X hX f),
    Lp.coeFn_compMeasurePreserving f hX] with ω h1 h2 h3 h4
  change Lp.compMeasurePreserving X hX (sine ν f) ω=_
  rw [h1,Function.comp_apply,h2,h3]
  congr 1
  change f (X ω)=Lp.compMeasurePreserving X hX f ω
  exact h4.symm

theorem polynomial_pullback (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (cols : κ → Lp ℝ 2 ν) :
    Lp.compMeasurePreservingₗ ℝ X hX (polynomial ν s b cols)=
      polynomial μ s b (fun k => Lp.compMeasurePreservingₗ ℝ X hX (cols k)) := by
  simp only [polynomial,map_sum,map_smul,sine_pullback,linear]

theorem readout_pullback (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (cols : κ → Lp ℝ 2 ν) :
    Lp.compMeasurePreservingₗ ℝ X hX (readout ν s b cols)=
      readout μ s b (fun k => Lp.compMeasurePreservingₗ ℝ X hX (cols k)) := by
  simp only [readout,sine_pullback,map_smul,polynomial_pullback]

 

def coefficientBound (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) : ℝ :=
  ∑a∈s, |b a| * (∑k, |a k|)

theorem coefficientBound_nonneg (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ) :
    0≤coefficientBound s b := by
  exact Finset.sum_nonneg (fun a ha => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem polynomial_norm_sub_uniform (s : Finset (κ → ℝ)) (b : (κ → ℝ) → ℝ)
    (f g : κ → Lp ℝ 2 μ) {δ : ℝ} (h : ∀k, ‖f k-g k‖≤δ) :
    ‖polynomial μ s b f-polynomial μ s b g‖≤coefficientBound s b*δ := by
  calc
    _ ≤ ∑a∈s, |b a| *(∑k, |a k| *‖f k-g k‖) := polynomial_norm_sub_le μ s b f g
    _ ≤ ∑a∈s, |b a| *(∑k, |a k| *δ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (h k) (abs_nonneg _))
    _ = coefficientBound s b*δ := by
      simp only [coefficientBound,Finset.sum_mul,Finset.mul_sum,mul_assoc]

end TrigLp

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory TrigLp
universe u v
variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {κ : Type*} [Fintype κ]

 

def localValue (cols : κ → E) (φ : (κ → ℝ) → ℝ)
    (hφ : MemLp φ 2 (inputLaw (stdGaussian E) (fun k => aggregate E (cols k)))) :
    Lp ℝ 2 (stdGaussian E) :=
  (hφ.comp_measurePreserving (inputMap_preserving (stdGaussian E)
    (fun k => aggregate E (cols k)))).toLp
      (φ ∘ inputMap (stdGaussian E) (fun k => aggregate E (cols k)))

 

theorem exists_ambient_robust_operation (cols : κ → E) (φ : (κ → ℝ) → ℝ)
    (hφ : MemLp φ 2 (inputLaw (stdGaussian E) (fun k => aggregate E (cols k))))
    (ho : ∀x, φ (-x)= -φ x) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀ (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
        (i : E →ₗᵢ[ℝ] F) (d : κ → F), (∀k, ‖d k-i (cols k)‖<δ) →
          ‖polynomial (stdGaussian F) s b (fun k => aggregate F (d k))-
            Lp.compMeasurePreservingₗ ℝ (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
              (projection_preserving i) (localValue E cols φ hφ)‖<ε := by
  obtain ⟨s,b,δ₀,hδ₀,ha⟩ := exists_robust_gaussian_operation E cols φ hφ ho (half_pos hε)
  have hb := ha cols (fun k => by simpa only [sub_self,norm_zero] using hδ₀)
  change ‖polynomial (stdGaussian E) s b (fun k => aggregate E (cols k))-
    localValue E cols φ hφ‖<ε/2 at hb
  let K := coefficientBound s b
  have hK : 0≤K := coefficientBound_nonneg s b
  have hp : 0<2*(K+1) := by positivity
  let δ := ε/(2*(K+1))
  have hδ : 0<δ := div_pos hε hp
  have heq : δ*(2*(K+1))=ε := div_mul_cancel₀ ε (ne_of_gt hp)
  have hKδ : K*δ<ε/2 := by nlinarith
  refine ⟨s,b,δ,hδ,?_⟩
  intro F inst1 inst2 inst3 inst4 inst5 i d hd
  let P : Lp ℝ 2 (stdGaussian E) →ₗ[ℝ] Lp ℝ 2 (stdGaussian F) := Lp.compMeasurePreservingₗ ℝ
    (ContinuousLinearMap.adjoint i.toContinuousLinearMap) (projection_preserving i)
  have hid : polynomial (stdGaussian F) s b (fun k => aggregate F (i (cols k)))=
      P (polynomial (stdGaussian E) s b (fun k => aggregate E (cols k))) := by
    rw [polynomial_pullback]
    congr 1
    funext k
    exact (aggregate_pullback i (cols k)).symm
  have herr : ‖polynomial (stdGaussian F) s b (fun k => aggregate F (i (cols k)))-
      P (localValue E cols φ hφ)‖<ε/2 := by
    rw [hid,←map_sub]
    change ‖Lp.compMeasurePreserving (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
      (projection_preserving i)
      (polynomial (stdGaussian E) s b (fun k => aggregate E (cols k))-localValue E cols φ hφ)‖<ε/2
    rwa [Lp.norm_compMeasurePreserving]
  have hpert : ‖polynomial (stdGaussian F) s b (fun k => aggregate F (d k))-
      polynomial (stdGaussian F) s b (fun k => aggregate F (i (cols k)))‖<ε/2 := by
    apply lt_of_le_of_lt (polynomial_norm_sub_uniform (stdGaussian F) s b _ _ ?_) hKδ
    intro k
    rw [norm_aggregate_sub]
    exact (hd k).le
  calc
    _ ≤ ‖polynomial (stdGaussian F) s b (fun k => aggregate F (d k))-
        polynomial (stdGaussian F) s b (fun k => aggregate F (i (cols k)))‖+
      ‖polynomial (stdGaussian F) s b (fun k => aggregate F (i (cols k)))-
        P (localValue E cols φ hφ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add hpert herr
    _ = ε := add_halves ε

end ClassicalGaussian

namespace ClassicalGaussian
open MeasureTheory ProbabilityTheory TrigLp
universe u v
variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {κ : Type*} [Fintype κ]

 

theorem exists_ambient_robust_angle (cols : κ → E) (φ : (κ → ℝ) → ℝ)
    (hφ : MemLp φ 2 (inputLaw (stdGaussian E) (fun k => aggregate E (cols k))))
    (ho : ∀x, φ (-x)= -φ x) (hbound : ∀x, |φ x|≤1) {ε : ℝ} (hε : 0<ε) :
    ∃s : Finset (κ → ℝ), ∃b : (κ → ℝ) → ℝ, ∃δ : ℝ, 0<δ ∧
      ∀ (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
        (i : E →ₗᵢ[ℝ] F) (d : κ → F), (∀k, ‖d k-i (cols k)‖<δ) →
          ‖readout (stdGaussian F) s b (fun k => aggregate F (d k))-
            Lp.compMeasurePreservingₗ ℝ (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
              (projection_preserving i) (localValue E cols φ hφ)‖<ε := by
  obtain ⟨s,b,δ₀,hδ₀,ha⟩ := exists_robust_gaussian_angle E cols φ hφ ho hbound (half_pos hε)
  have hb := ha cols (fun k => by simpa only [sub_self,norm_zero] using hδ₀)
  change ‖readout (stdGaussian E) s b (fun k => aggregate E (cols k))-
    localValue E cols φ hφ‖<ε/2 at hb
  let K := coefficientBound s b
  have hK : 0≤K := coefficientBound_nonneg s b
  have hp : 0<4*(K+1) := by positivity
  let δ := ε/(4*(K+1))
  have hδ : 0<δ := div_pos hε hp
  have heq : δ*(4*(K+1))=ε := div_mul_cancel₀ ε (ne_of_gt hp)
  have hKδ : 2*(K*δ)<ε/2 := by nlinarith
  refine ⟨s,b,δ,hδ,?_⟩
  intro F inst1 inst2 inst3 inst4 inst5 i d hd
  let P : Lp ℝ 2 (stdGaussian E) →ₗ[ℝ] Lp ℝ 2 (stdGaussian F) := Lp.compMeasurePreservingₗ ℝ
    (ContinuousLinearMap.adjoint i.toContinuousLinearMap) (projection_preserving i)
  have hid : readout (stdGaussian F) s b (fun k => aggregate F (i (cols k)))=
      P (readout (stdGaussian E) s b (fun k => aggregate E (cols k))) := by
    rw [readout_pullback]
    congr 1
    funext k
    exact (aggregate_pullback i (cols k)).symm
  have herr : ‖readout (stdGaussian F) s b (fun k => aggregate F (i (cols k)))-
      P (localValue E cols φ hφ)‖<ε/2 := by
    rw [hid,←map_sub]
    change ‖Lp.compMeasurePreserving (ContinuousLinearMap.adjoint i.toContinuousLinearMap)
      (projection_preserving i)
      (readout (stdGaussian E) s b (fun k => aggregate E (cols k))-localValue E cols φ hφ)‖<ε/2
    rwa [Lp.norm_compMeasurePreserving]
  have hpert : ‖readout (stdGaussian F) s b (fun k => aggregate F (d k))-
      readout (stdGaussian F) s b (fun k => aggregate F (i (cols k)))‖<ε/2 := by
    apply lt_of_le_of_lt (readout_norm_sub_le (stdGaussian F) s b _ _)
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (polynomial_norm_sub_uniform (stdGaussian F) s b _ _ ?_) (by norm_num : (0:ℝ)≤2)) hKδ
    intro k
    rw [norm_aggregate_sub]
    exact (hd k).le
  calc
    _ ≤ ‖readout (stdGaussian F) s b (fun k => aggregate F (d k))-
        readout (stdGaussian F) s b (fun k => aggregate F (i (cols k)))‖+
      ‖readout (stdGaussian F) s b (fun k => aggregate F (i (cols k)))-
        P (localValue E cols φ hφ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε/2+ε/2 := add_lt_add hpert herr
    _ = ε := add_halves ε

end ClassicalGaussian

namespace FiniteOccupations
open scoped InnerProductSpace BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
variable (f : A → B)

def weight (b : B) : ℂ := (Real.sqrt (Fintype.card {a : A // f a=b} : ℝ) : ℂ)⁻¹

omit [Fintype B] in
theorem card_pos (hf : Function.Surjective f) (b : B) : 0<Fintype.card {a : A // f a=b} := by
  obtain ⟨a,ha⟩ := hf b
  exact Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩

omit [Fintype B] in
@[simp] theorem star_weight (b : B) : starRingEnd ℂ (weight f b)=weight f b := by
  simp [weight]

omit [Fintype B] in
theorem card_mul_weight_sq (hf : Function.Surjective f) (b : B) :
    (Fintype.card {a : A // f a=b} : ℂ)*(weight f b)^2=1 := by
  have hsq : (Real.sqrt (Fintype.card {a : A // f a=b} : ℝ) : ℂ)^2=
      (Fintype.card {a : A // f a=b} : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card {a : A // f a=b}))
  rw [weight,inv_pow,hsq]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (card_pos f hf b)))

omit [Fintype B] in
theorem weight_ne_zero (hf : Function.Surjective f) (b : B) : weight f b≠0 := by
  intro h
  simpa [h] using card_mul_weight_sq f hf b

 

def liftLinear : EuclideanSpace ℂ B →ₗ[ℂ] EuclideanSpace ℂ A where
  toFun u := WithLp.toLp 2 (fun a => weight f (f a)*u (f a))
  map_add' u v := by ext a; simp [mul_add]
  map_smul' c u := by ext a; simp [mul_left_comm]

omit [Fintype B] in
@[simp] theorem liftLinear_apply (u : EuclideanSpace ℂ B) (a : A) :
    liftLinear f u a=weight f (f a)*u (f a) := rfl

 
theorem inner_lift (hf : Function.Surjective f) (u v : EuclideanSpace ℂ B) :
    ⟪liftLinear f u,liftLinear f v⟫_ℂ=⟪u,v⟫_ℂ := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply,liftLinear_apply,map_mul,star_weight]
  rw [←Fintype.sum_fiberwise f]
  apply Finset.sum_congr rfl
  intro b hb
  have he (a : {a : A // f a=b}) :
      weight f (f a)*v (f a)*(weight f (f a)*starRingEnd ℂ (u (f a)))=
        (weight f b)^2*(v b*starRingEnd ℂ (u b)) := by rw [a.property]; ring
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←mul_assoc,card_mul_weight_sq f hf,one_mul]

 

def lift (hf : Function.Surjective f) : EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ A :=
  LinearMap.isometryOfInner (liftLinear f) (inner_lift f hf)

@[simp] theorem lift_apply (hf : Function.Surjective f) (u : EuclideanSpace ℂ B) (a : A) :
    lift f hf u a=weight f (f a)*u (f a) := rfl

 
theorem mem_range_iff (hf : Function.Surjective f) (u : EuclideanSpace ℂ A) :
    u∈Set.range (lift f hf) ↔ ∀a a', f a=f a' → u a=u a' := by
  constructor
  · rintro ⟨v,rfl⟩ a a' h
    simp only [lift_apply,h]
  · intro h
    let rep : B → A := fun b => (hf b).choose
    have hr (b : B) : f (rep b)=b := (hf b).choose_spec
    refine ⟨WithLp.toLp 2 (fun b => u (rep b)/weight f b),?_⟩
    ext a
    change weight f (f a)*(u (rep (f a))/weight f (f a))=u a
    rw [mul_div_cancel₀ _ (weight_ne_zero f hf _)]
    exact h _ _ (hr (f a))

end FiniteOccupations

namespace FiniteTensorOccupations
open scoped InnerProductSpace
variable {I α : Type*} [Fintype I] [Fintype α] [DecidableEq α]
local instance : DecidableEq I := Classical.decEq _

 
def counts (w : I → α) (a : α) : ℕ := Fintype.card {i : I // w i=a}

omit [Fintype α] in
theorem counts_eq_iff (w z : I → α) :
    counts w=counts z ↔ ∃σ : I ≃ I, ∀i, z (σ i)=w i := by
  classical
  constructor
  · intro h
    let e (a : α) : {i : I // w i=a} ≃ {i : I // z i=a} :=
      Fintype.equivOfCardEq (congrFun h a)
    exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩
  · rintro ⟨σ,hσ⟩
    funext a
    apply Fintype.card_congr
    exact {
      toFun := fun i => ⟨σ i,by rw [hσ,i.property]⟩
      invFun := fun j => ⟨σ.symm j,by rw [←hσ,σ.apply_symm_apply,j.property]⟩
      left_inv := by intro i; ext; simp
      right_inv := by intro j; ext; simp }

def occupancySetoid : Setoid (I → α) where
  r w z := counts w=counts z
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h h' => h.trans h'⟩

 
abbrev Occupation (I α : Type*) [Fintype I] [DecidableEq α] :=
  Quotient (occupancySetoid (I := I) (α := α))

instance : Fintype (Occupation I α) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Occupation I α) := Classical.decEq _

def register (w : I → α) : Occupation I α := Quotient.mk _ w

omit [Fintype α] in
@[simp] theorem register_eq_iff (w z : I → α) :
    register w=register z ↔ counts w=counts z := Quotient.eq

omit [Fintype α] in
theorem register_surjective : Function.Surjective (register (I := I) (α := α)) := by
  intro q
  exact Quotient.inductionOn q (fun w => ⟨w,rfl⟩)

 

def embedding : EuclideanSpace ℂ (Occupation I α) →ₗᵢ[ℂ] EuclideanSpace ℂ (I → α) :=
  FiniteOccupations.lift register register_surjective

 

theorem mem_range_iff_symmetric (u : EuclideanSpace ℂ (I → α)) :
    u∈Set.range (embedding (I := I) (α := α)) ↔
      ∀w : I → α, ∀σ : I ≃ I, u (w ∘ σ)=u w := by
  rw [embedding,FiniteOccupations.mem_range_iff]
  constructor
  · intro h w σ
    apply h
    apply (register_eq_iff _ _).mpr
    exact (counts_eq_iff _ _).mpr ⟨σ,fun _ => rfl⟩
  · intro h w z hwz
    obtain ⟨σ,hσ⟩ := (counts_eq_iff w z).mp ((register_eq_iff _ _).mp hwz)
    have he : z ∘ σ=w := funext hσ
    simpa only [he] using h z σ

 
def symmetricSector : Submodule ℂ (EuclideanSpace ℂ (I → α)) where
  carrier := {u | ∀w : I → α, ∀σ : I ≃ I, u (w ∘ σ)=u w}
  zero_mem' := by intro w σ; rfl
  add_mem' := by intro u v hu hv w σ; simp [hu w σ,hv w σ]
  smul_mem' := by intro c u hu w σ; simp [hu w σ]

 
def symmetricEmbedding :
    EuclideanSpace ℂ (Occupation I α) →ₗᵢ[ℂ] symmetricSector (I := I) (α := α) where
  toLinearMap := (embedding (I := I) (α := α)).toLinearMap.codRestrict symmetricSector
    (fun u => (mem_range_iff_symmetric _).mp ⟨u,rfl⟩)
  norm_map' u := (embedding (I := I) (α := α)).norm_map u

theorem symmetricEmbedding_surjective :
    Function.Surjective (symmetricEmbedding (I := I) (α := α)) := by
  intro y
  obtain ⟨u,hu⟩ := (mem_range_iff_symmetric (y : EuclideanSpace ℂ (I → α))).mpr y.property
  refine ⟨u,?_⟩
  apply Subtype.ext
  exact hu

 

def occupationMap : symmetricSector (I := I) (α := α) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ (Occupation I α) :=
  (LinearIsometryEquiv.ofSurjective symmetricEmbedding symmetricEmbedding_surjective).symm

@[simp] theorem occupationMap_symm_apply (u : EuclideanSpace ℂ (Occupation I α))
    (w : I → α) :
    (occupationMap.symm u : EuclideanSpace ℂ (I → α)) w =
      FiniteOccupations.weight register (register w)*u (register w) := rfl

end FiniteTensorOccupations

end

end OAI
