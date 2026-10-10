import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGenerator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


namespace WeakHessianFunctional

section QuadraticScaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
variable [CompleteSpace E]
include hQ

omit [CompleteSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] hQ in
lemma ClosedQuadraticEnergy.scale_lt_top_iff {t : ℝ} (ht : 0 < t) (u : E) :
    ENNReal.ofReal t * Q u < ∞ ↔ Q u < ∞ := by
  rw [ENNReal.mul_lt_top_iff]
  simp only [ENNReal.ofReal_lt_top, true_and, ENNReal.ofReal_eq_zero,
    not_le.mpr ht, false_or]
  constructor
  · rintro (hu | hu)
    · exact hu
    · simp [hu]
  · exact Or.inl

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale {t : ℝ} (ht : 0 < t) :
    ClosedQuadraticEnergy (fun u => ENNReal.ofReal t*Q u) where
  lowerSemicontinuous := (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
    hQ.lowerSemicontinuous (fun _ _ h => mul_le_mul_right h _)
  zero := by rw [hQ.zero, mul_zero]
  smul := by intro c u; rw [hQ.smul]; ac_rfl
  parallelogram := by
    intro u v hu hv
    rw [← mul_add, hQ.parallelogram u v ((ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mp hu)
      ((ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mp hv), mul_add]
    congr 1 <;> ac_rfl

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale_form {t : ℝ} (ht : 0 < t) (u v : E)
    (hu : Q u < ∞) (hv : Q v < ∞) :
    (hQ.scale ht).form ⟨u,(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mpr hu⟩
      ⟨v,(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mpr hv⟩ =
      t*hQ.form ⟨u,hu⟩ ⟨v,hv⟩ := by
  rw [ClosedQuadraticEnergy.form_apply, ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar, ClosedQuadraticEnergy.realEnergy, Submodule.coe_add,
    Submodule.coe_sub, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le]
  ring

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale_isFormGenerator_iff {t : ℝ} (ht : 0 < t) (u A : E) :
    (hQ.scale ht).IsFormGenerator u (t • A) ↔ hQ.IsFormGenerator u A := by
  constructor
  · rintro ⟨hu,hgen⟩
    have hu' := (ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mp hu
    refine ⟨hu', ?_⟩
    intro v
    have H := hgen ⟨(v:E),(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mpr v.property⟩
    rw [hQ.scale_form ht u v hu' v.property, real_inner_smul_left] at H
    change 2*hQ.form ⟨u,hu'⟩ v = -⟪A,(v:E)⟫_ℝ
    nlinarith
  · rintro ⟨hu,hgen⟩
    refine ⟨(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mpr hu, ?_⟩
    intro v
    have hv := (ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mp v.property
    have H := hgen ⟨(v:E),hv⟩
    rw [hQ.scale_form ht u v hu hv, real_inner_smul_left]
    nlinarith

lemma ClosedQuadraticEnergy.scaled_resolvent_iff {t : ℝ} (ht : 0 < t) (u v : E) :
    (hQ.scale ht).resolvent u = v ↔ hQ.IsFormGenerator v (t⁻¹ • (v-u)) := by
  rw [← hQ.scale_isFormGenerator_iff ht]
  simp only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [(hQ.scale ht).isFormGenerator_iff, sub_sub_cancel]

end QuadraticScaling

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

def reLp : Lp ℂ 2 m →L[ℝ] Lp ℝ 2 m := Complex.reCLM.compLpL 2 m
def imLp : Lp ℂ 2 m →L[ℝ] Lp ℝ 2 m := Complex.imCLM.compLpL 2 m
def ofRealLp : Lp ℝ 2 m →L[ℝ] Lp ℂ 2 m := Complex.ofRealCLM.compLpL 2 m

lemma reLp_ae (f : Lp ℂ 2 m) : reLp m f =ᵐ[m] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f
lemma imLp_ae (f : Lp ℂ 2 m) : imLp m f =ᵐ[m] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f
lemma ofRealLp_ae (f : Lp ℝ 2 m) : ofRealLp m f =ᵐ[m] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

@[simp] lemma re_ofRealLp (f : Lp ℝ 2 m) : reLp m (ofRealLp m f) = f := by
  apply Lp.ext
  filter_upwards [reLp_ae m (ofRealLp m f), ofRealLp_ae m f] with x hr hf
  simp [hr,hf]
@[simp] lemma im_ofRealLp (f : Lp ℝ 2 m) : imLp m (ofRealLp m f) = 0 := by
  apply Lp.ext
  filter_upwards [imLp_ae m (ofRealLp m f), ofRealLp_ae m f, Lp.coeFn_zero ℝ 2 m] with x hr hf hz
  rw [hr,hf,hz]
  rfl

lemma reLp_smul_complex (c : ℂ) (f : Lp ℂ 2 m) :
    reLp m (c • f) = c.re • reLp m f - c.im • imLp m f := by
  apply Lp.ext
  filter_upwards [reLp_ae m (c • f), reLp_ae m f, imLp_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_sub (c.re • reLp m f) (c.im • imLp m f),
    Lp.coeFn_smul c.re (reLp m f), Lp.coeFn_smul c.im (imLp m f)] with x h1 h2 h3 h4 h5 h6 h7
  simp only [h1,h4,h5, Pi.sub_apply, h6,h7, Pi.smul_apply, h2,h3, smul_eq_mul, Complex.mul_re]

lemma imLp_smul_complex (c : ℂ) (f : Lp ℂ 2 m) :
    imLp m (c • f) = c.re • imLp m f + c.im • reLp m f := by
  apply Lp.ext
  filter_upwards [imLp_ae m (c • f), reLp_ae m f, imLp_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_add (c.re • imLp m f) (c.im • reLp m f),
    Lp.coeFn_smul c.re (imLp m f), Lp.coeFn_smul c.im (reLp m f)] with x h1 h2 h3 h4 h5 h6 h7
  simp only [h1,h4,h5, Pi.add_apply, h6,h7, Pi.smul_apply, h2,h3, smul_eq_mul, Complex.mul_im]

lemma ofRealLp_re_add_im (f : Lp ℂ 2 m) :
    ofRealLp m (reLp m f) + Complex.I • ofRealLp m (imLp m f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofRealLp m (reLp m f)) (Complex.I • ofRealLp m (imLp m f)),
    Lp.coeFn_smul Complex.I (ofRealLp m (imLp m f)), ofRealLp_ae m (reLp m f),
    ofRealLp_ae m (imLp m f), reLp_ae m f, imLp_ae m f] with x ha hs hr hi hf hg
  simp only [ha, Pi.add_apply, hs, Pi.smul_apply, hr,hi,hf,hg, smul_eq_mul]
  simpa only [mul_comm] using Complex.re_add_im (f x)

lemma ofRealLp_inner (f g : Lp ℝ 2 m) :
    ⟪ofRealLp m f, ofRealLp m g⟫_ℂ = (⟪f,g⟫_ℝ : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ofRealLp_ae m f, ofRealLp_ae m g] with x hf hg
  simp [hf,hg, RCLike.inner_apply]

lemma complexLp_inner (f g : Lp ℂ 2 m) :
    ⟪f,g⟫_ℂ = (⟪reLp m f,reLp m g⟫_ℝ : ℂ) + (⟪imLp m f,imLp m g⟫_ℝ : ℂ) +
      ((⟪reLp m f,imLp m g⟫_ℝ : ℂ) - (⟪imLp m f,reLp m g⟫_ℝ : ℂ))*Complex.I := by
  conv_lhs => rw [← ofRealLp_re_add_im m f, ← ofRealLp_re_add_im m g]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    ofRealLp_inner, Complex.conj_I]
  ring_nf
  simp

def complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Lp ℂ 2 m →L[ℝ] Lp ℂ 2 m :=
  (ofRealLp m).comp (R.comp (reLp m)) +
    Complex.I • (ofRealLp m).comp (R.comp (imLp m))

lemma complexifyReal_apply (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    complexifyReal m R f = ofRealLp m (R (reLp m f)) +
      Complex.I • ofRealLp m (R (imLp m f)) := rfl

lemma complexLp_ext {f g : Lp ℂ 2 m}
    (hr : reLp m f = reLp m g) (hi : imLp m f = imLp m g) : f = g := by
  rw [← ofRealLp_re_add_im m f, hr, hi, ofRealLp_re_add_im]

@[simp] lemma re_complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    reLp m (complexifyReal m R f) = R (reLp m f) := by
  simp [complexifyReal_apply, reLp_smul_complex]

@[simp] lemma im_complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    imLp m (complexifyReal m R f) = R (imLp m f) := by
  simp [complexifyReal_apply, imLp_smul_complex]

lemma complexifyReal_smul (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (c : ℂ) (f : Lp ℂ 2 m) :
    complexifyReal m R (c • f) = c • complexifyReal m R f := by
  apply complexLp_ext m
  · simp [reLp_smul_complex]
  · simp [imLp_smul_complex]

def complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m where
  toFun := complexifyReal m R
  map_add' := (complexifyReal m R).map_add
  map_smul' := complexifyReal_smul m R
  cont := (complexifyReal m R).continuous

@[simp] lemma re_complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    reLp m (complexify m R f) = R (reLp m f) := re_complexifyReal m R f
@[simp] lemma im_complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    imLp m (complexify m R f) = R (imLp m f) := im_complexifyReal m R f

lemma complexify_symmetric {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.toLinearMap.IsSymmetric) : (complexify m R).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪complexify m R f,g⟫_ℂ = ⟪f,complexify m R g⟫_ℂ
  simp only [complexLp_inner, re_complexify, im_complexify]
  have hr (u v : Lp ℝ 2 m) : ⟪R u,v⟫_ℝ = ⟪u,R v⟫_ℝ := hR u v
  simp only [hr]

lemma complexify_injective {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : Function.Injective R) : Function.Injective (complexify m R) := by
  intro f g h
  apply complexLp_ext m
  · apply hR
    simpa using congrArg (reLp m) h
  · apply hR
    simpa using congrArg (imLp m) h

lemma complexify_positive {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) : (complexify m R).IsPositive := by
  refine ⟨complexify_symmetric m hR.isSymmetric, ?_⟩
  intro f
  change 0 ≤ (⟪complexify m R f,f⟫_ℂ).re
  rw [complexLp_inner]
  simp only [re_complexify, im_complexify, Complex.add_re, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, zero_mul, add_zero]
  exact add_nonneg (hR.re_inner_nonneg_left _) (hR.re_inner_nonneg_left _)

lemma complexify_sub (R S : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) :
    complexify m (R-S) = complexify m R-complexify m S := by
  ext1 f
  apply complexLp_ext m <;> simp

lemma complexify_one : complexify m (1 : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) = 1 := by
  ext1 f
  apply complexLp_ext m <;> simp

lemma complexify_range_dense {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hs : R.toLinearMap.IsSymmetric) (hi : Function.Injective R) :
    (complexify m R).toLinearMap.range.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply complexify_injective m hi
  rw [map_zero]
  have hz : ∀ w, ⟪w,complexify m R u⟫_ℂ = 0 := by
    intro w
    exact ((complexify_symmetric m hs) w u).symm.trans
      ((Submodule.mem_orthogonal _ _).mp hu (complexify m R w) ⟨w,rfl⟩)
  exact inner_self_eq_zero.mp (hz (complexify m R u))

lemma ofRealLp_of_im_zero {f : Lp ℂ 2 m} (hf : imLp m f = 0) :
    ofRealLp m (reLp m f) = f := by
  simpa [hf] using ofRealLp_re_add_im m f

local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
local instance : StarModule ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) where
  star_smul scalar operator := by
    rw [← smul_one_smul ℂ scalar operator, star_smul, star_smul, star_one, smul_one_smul]

def realOperators : StarSubalgebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) where
  carrier := {T | ∀ f : Lp ℝ 2 m, imLp m (T (ofRealLp m f)) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS f
    change imLp m (T (ofRealLp m f) + S (ofRealLp m f)) = 0
    simp [hT f,hS f]
  one_mem' := by simp
  mul_mem' := by
    intro T S hT hS f
    change imLp m (T (S (ofRealLp m f))) = 0
    rw [← ofRealLp_of_im_zero m (hS f)]
    exact hT _
  algebraMap_mem' := by
    intro r f
    change imLp m (r • ofRealLp m f) = 0
    simp
  star_mem' := by
    intro T hT f
    let v := imLp m ((star T) (ofRealLp m f))
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have he := congrArg Complex.im
      (ContinuousLinearMap.adjoint_inner_left T (ofRealLp m v) (ofRealLp m f))
    change (⟪(star T) (ofRealLp m f),ofRealLp m v⟫_ℂ).im =
      (⟪ofRealLp m f,T (ofRealLp m v)⟫_ℂ).im at he
    simp only [complexLp_inner, re_ofRealLp, im_ofRealLp, hT v, inner_zero_right,
      inner_zero_left, Complex.ofReal_zero, add_zero, zero_sub, sub_zero,
      Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.neg_im, Complex.neg_re, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one] at he
    change ⟪v,v⟫_ℝ = 0
    linarith

lemma realOperators_closed : IsClosed (realOperators m : Set (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m)) := by
  change IsClosed {T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m | ∀ f : Lp ℝ 2 m,
    imLp m (T (ofRealLp m f)) = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro f
  exact isClosed_eq ((imLp m).continuous.comp (ContinuousLinearMap.apply ℂ _ (ofRealLp m f)).continuous)
    continuous_const

lemma complexify_mem_realOperators (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) :
    complexify m R ∈ realOperators m := by
  intro f
  simp

lemma cfc_preserves_real (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (f : Lp ℝ 2 m) : imLp m (cfc a (complexify m R) (ofRealLp m f)) = 0 := by
  have hle : StarAlgebra.elemental ℝ (complexify m R) ≤ realOperators m :=
    StarAlgebra.elemental.le_of_mem (realOperators_closed m) (complexify_mem_realOperators m R)
  exact hle (cfc_mem_elemental a (complexify m R)) f

def realCfc (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  (reLp m).comp (((cfc a (complexify m R)).restrictScalars ℝ).comp (ofRealLp m))

lemma ofReal_realCfc (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (f : Lp ℝ 2 m) : ofRealLp m (realCfc m R a f) = cfc a (complexify m R) (ofRealLp m f) :=
  ofRealLp_of_im_zero m (cfc_preserves_real m R a f)

end WeakHessianFunctional

open Set Filter
open scoped Topology

end

end OAI
