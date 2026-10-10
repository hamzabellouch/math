import OAI.Analysis.LiebThirring.FieldRegularity

namespace OAI

universe u32 u33 u34

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u32} [Fintype n] [DecidableEq n]

-- Select the inherited subspace seminorm, avoiding the duplicate subgroup
-- class instance during elaboration of iterated continuous-linear maps.
local instance : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def traceGradientMap : Matrix n n ℂ →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun M ↦ (tracePairCLM M).comp hermitianInclusion
    map_add' := by
      intro M N
      ext H
      simp [tracePairCLM_apply, hermitianInclusion, add_mul, trace_add]
    map_smul' := by
      intro r M
      ext H
      simp [tracePairCLM_apply, hermitianInclusion, trace_smul] }

@[simp] lemma traceGradientMap_apply (M : Matrix n n ℂ) (B : selfAdjoint (Matrix n n ℂ)) :
    traceGradientMap M B = (trace (M * (B : Matrix n n ℂ))).re := rfl

def traceGradientNorm : ℝ := ‖traceGradientMap (n := n)‖

lemma traceGradientNorm_nonneg : 0 ≤ traceGradientNorm (n := n) :=
  (traceGradientMap (n := n)).opNorm_nonneg

lemma traceGradientMap_bound (M : Matrix n n ℂ) :
    ‖traceGradientMap M‖ ≤ traceGradientNorm (n := n) * ‖M‖ := by
  have hh := (traceGradientMap (n := n)).le_opNorm M
  convert! hh

def quadraticSelfAdjoint (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ)
    (B : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  C - (2 * s) • B + (s ^ 2) • 1

@[simp] lemma quadraticSelfAdjoint_coe (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ)
    (B : selfAdjoint (Matrix n n ℂ)) :
    (quadraticSelfAdjoint C s B : Matrix n n ℂ) = quadraticMatrix C B s := by
  simp [quadraticSelfAdjoint, quadraticMatrix, add_comm]

lemma quadraticSelfAdjoint_hasFDerivAt (C B : selfAdjoint (Matrix n n ℂ)) (s : ℝ) :
    HasFDerivAt (quadraticSelfAdjoint C s) ((-2 * s) • ContinuousLinearMap.id ℝ _) B := by
  convert! (((hasFDerivAt_id (𝕜 := ℝ) B).const_smul (2 * s)).const_sub C).add_const ((s ^ 2) • 1) using 1
  ext H : 1
  change (-2 * s) • H = -((2 * s) • H)
  module

/-- Paired trace potential. At s=0 the assigned value is immaterial to its integral. -/
def pairedTracePotential (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ))
    (B : selfAdjoint (Matrix n n ℂ)) (s : ℝ) : ℝ :=
  -( (trace (cfc (secondPrimitive σ δ) (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s))).re -
    (trace (cfc (secondPrimitive σ δ) (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) (-s)))).re) / (2 * s) -
      2 * regularizedPrimitive σ δ (s ^ 2) * (trace (B : Matrix n n ℂ)).re

lemma pairedTracePotential_zero (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ) :
    pairedTracePotential σ δ C 0 s = 0 := by
  simp [pairedTracePotential, quadraticMatrix]

lemma pairedTracePotential_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) {s : ℝ} (hs : s ≠ 0) :
    HasFDerivAt (fun B ↦ pairedTracePotential σ δ C B s)
      (traceGradientMap (pairedFieldIntegrand σ δ C B s)) B := by
  have h1 := (trace_secondPrimitive_hasFDerivAt hσ hδ (quadraticSelfAdjoint C s B)).comp B
    (quadraticSelfAdjoint_hasFDerivAt C B s)
  have h2 := (trace_secondPrimitive_hasFDerivAt hσ hδ (quadraticSelfAdjoint C (-s) B)).comp B
    (quadraticSelfAdjoint_hasFDerivAt C B (-s))
  have h3 := (traceGradientMap (1 : Matrix n n ℂ)).hasFDerivAt (x := B)
  have hh := ((h1.sub h2).neg.const_mul (2 * s)⁻¹).sub (h3.const_mul
    (2 * regularizedPrimitive σ δ (s ^ 2)))
  convert! hh using 1
  · funext D
    simp [pairedTracePotential, Function.comp_def, traceGradientMap_apply, div_eq_mul_inv, mul_comm]
  · ext H
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      _root_.neg_apply, traceGradientMap_apply, tracePairCLM_apply,
      quadraticSelfAdjoint_coe]
    change (trace (pairedFieldIntegrand σ δ C B s * (H : Matrix n n ℂ))).re = _
    simp only [pairedFieldIntegrand, sub_mul, add_mul, smul_mul_assoc, one_mul,
      trace_sub, trace_add, trace_smul, Complex.sub_re, Complex.add_re, Complex.real_smul,
      hermitianInclusion, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk, selfAdjoint.val_smul, mul_smul_comm, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [smul_eq_mul]
    field_simp [hs]
    ring

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u33} [Fintype n] [DecidableEq n]

-- Select the inherited subspace seminorm, avoiding the duplicate subgroup
-- class instance during elaboration of iterated continuous-linear maps.
local instance : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

lemma measurable_pairedTracePotential {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    (C B : selfAdjoint (Matrix n n ℂ)) : Measurable (pairedTracePotential σ δ C B) := by
  have hc : Continuous (fun s : ℝ ↦ cfc (secondPrimitive σ δ)
      (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (Filter.univ_mem)
      (by unfold quadraticMatrix; fun_prop)
      (fun s ↦ quadraticMatrix_hermitian C.prop B.prop s)
      (continuous_iff_continuousAt.mpr (fun y ↦ (secondPrimitive_hasDerivAt σ hδ y).continuousAt)).continuousOn
  have ht : Continuous (fun s : ℝ ↦ (trace (cfc (secondPrimitive σ δ)
      (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s))).re) := by fun_prop
  unfold pairedTracePotential
  exact (((ht.measurable.sub (ht.comp continuous_neg).measurable).neg).div
    (by fun_prop)).sub (((continuous_const.mul
      ((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2))).mul
        continuous_const).measurable)

def fieldGradientEnvelope (σ δ M : ℝ) (C : Matrix n n ℂ) (s : ℝ) : ℝ :=
  traceGradientNorm (n := n) *
    (‖pairedFieldIntegrand σ δ (C : Matrix n n ℂ) 0 s‖ + fieldLipEnvelope σ δ M (C : Matrix n n ℂ) s * M)

lemma integrable_fieldGradientEnvelope {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (M : ℝ) {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    Integrable (fieldGradientEnvelope σ δ M (C : Matrix n n ℂ)) :=
  ((integrable_pairedFieldIntegrand hσ hδ hC Matrix.isHermitian_zero).norm.add
    ((integrable_fieldLipEnvelope hσ M C).mul_const M)).const_mul _

lemma fieldGradientEnvelope_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C B : selfAdjoint (Matrix n n ℂ)) (hB : ‖B‖ ≤ M) (s : ℝ) :
    ‖traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)‖ ≤ fieldGradientEnvelope σ δ M (C : Matrix n n ℂ) s := by
  have hnorm := pairedFieldIntegrand_norm_on_ball hσ hδ hM C.prop B.prop hB s
  have hscaled := mul_le_mul_of_nonneg_left hnorm (traceGradientNorm_nonneg (n := n))
  have hop := traceGradientMap_bound (n := n)
    (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)
  have hr := le_trans hop hscaled
  convert! hr using 1


lemma pairedTracePotential_bound {σ δ M : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (C B : selfAdjoint (Matrix n n ℂ)) (hB : ‖B‖ ≤ M)
    {s : ℝ} (hs : s ≠ 0) :
    ‖pairedTracePotential σ δ C B s‖ ≤ fieldGradientEnvelope σ δ M (C : Matrix n n ℂ) s * ‖B‖ := by
  have hh := (convex_closedBall (0 : selfAdjoint (Matrix n n ℂ)) M).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (x := 0) (y := B)
    (fun A _ ↦ (pairedTracePotential_hasFDerivAt hσ hδ C A hs).hasFDerivWithinAt)
    (fun A hA ↦ fieldGradientEnvelope_bound hσ hδ hM C A (by simpa using hA) s)
    (by simpa using hM) (by simpa using hB)
  simpa only [pairedTracePotential_zero, sub_zero] using hh

lemma integrable_pairedTracePotential {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) : Integrable (pairedTracePotential σ δ C B) := by
  apply ((integrable_fieldGradientEnvelope hσ hδ ‖B‖ C.prop).mul_const ‖B‖).mono'
    (measurable_pairedTracePotential hδ σ C B).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
  exact pairedTracePotential_bound hσ hδ (norm_nonneg _) C B le_rfl hs

def hermitianPotential (σ δ : ℝ) (C B : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  (fieldNormalization σ / 2) * ∫ s : ℝ, pairedTracePotential σ δ C B s

lemma hermitianPotential_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (hermitianPotential σ δ C)
      (traceGradientMap (hermitianField σ δ C B)) B := by
  let M : ℝ := ‖B‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun A s ↦ pairedTracePotential σ δ C A s)
    (F' := fun (A : selfAdjoint (Matrix n n ℂ)) (s : ℝ) ↦
      traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (A : Matrix n n ℂ) s))
    (bound := fieldGradientEnvelope σ δ M (C : Matrix n n ℂ))
    (Metric.ball_mem_nhds B (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun A ↦ (measurable_pairedTracePotential hδ σ C A).aestronglyMeasurable))
    (integrable_pairedTracePotential hσ hδ C B)
    ((traceGradientMap.continuous.comp (continuous_pairedFieldIntegrand hδ σ C.prop B.prop)).aestronglyMeasurable)
    (Eventually.of_forall (fun s A hA ↦ fieldGradientEnvelope_bound hσ hδ hM C A
      (norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hA).le) s))
    (integrable_fieldGradientEnvelope hσ hδ M C.prop)
    (by filter_upwards [volume.ae_ne (0 : ℝ)] with s hs using fun A _ ↦
      pairedTracePotential_hasFDerivAt hσ hδ C A hs)
  have hi := (traceGradientMap (n := n)).integral_comp_comm (𝕜 := ℝ)
    (Fₗ := selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ)
    (integrable_pairedFieldIntegrand hσ hδ C.prop B.prop)
  have he : (∫ s : ℝ, traceGradientMap (pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s)) =
      traceGradientMap (∫ s : ℝ, pairedFieldIntegrand σ δ (C : Matrix n n ℂ) (B : Matrix n n ℂ) s) := by
    convert! hi
  rw [he] at hh
  convert! hh.const_smul (fieldNormalization σ / 2) using 1
  simp [hermitianField]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u34} [Fintype n] [DecidableEq n]

local instance : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

@[simp] lemma hermitianPotential_zero (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ)) :
    hermitianPotential σ δ C 0 = 0 := by
  simp [hermitianPotential, pairedTracePotential_zero]

lemma hermitianPotential_radial_hasDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ hermitianPotential σ δ C (t • B))
      (traceGradientMap (hermitianField σ δ C (t • B)) B) t := by
  convert! (hermitianPotential_hasFDerivAt hσ hδ C (t • B)).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const B) using 1
  simp

lemma hermitianPotential_radial {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) :
    hermitianPotential σ δ C B =
      ∫ t in (0 : ℝ)..1, (trace ((B : Matrix n n ℂ) * hermitianField σ δ C (t • B))).re := by
  have hc : Continuous (fun t : ℝ ↦ hermitianField σ δ (C : Matrix n n ℂ) (t • B)) := by
    have hcf := (hermitianField_locallyLipschitz hσ hδ C.prop).continuous
    have hsm : Continuous (fun t : ℝ ↦ t • B) := by fun_prop
    have hh := hcf.comp hsm
    convert! hh
  have ht : Continuous (fun t : ℝ ↦ traceGradientMap (hermitianField σ δ C (t • B)) B) := by
    simp only [traceGradientMap_apply]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hermitianPotential_radial_hasDerivAt hσ hδ C B t)
    (ht.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, hermitianPotential_zero, sub_zero] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro t _
  change traceGradientMap (hermitianField σ δ C (t • B)) B = _
  rw [traceGradientMap_apply, trace_mul_comm]

/-- The potential is a genuine trace primitive, not a radial definition
whose derivative has been assumed. -/
lemma radial_trace_hasFDerivAt {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (C B : selfAdjoint (Matrix n n ℂ)) :
    HasFDerivAt (fun B : selfAdjoint (Matrix n n ℂ) ↦
      -(∫ t in (0 : ℝ)..1, (trace ((B : Matrix n n ℂ) * hermitianField σ δ C (t • B))).re))
      (-traceGradientMap (hermitianField σ δ C B)) B := by
  convert! (hermitianPotential_hasFDerivAt hσ hδ C B).neg using 1
  funext A
  change -_ = -hermitianPotential σ δ C A
  rw [hermitianPotential_radial hσ hδ]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def realHermitianComplexify (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    selfAdjoint (Matrix (Fin N) (Fin N) ℂ) := ⟨complexify B, complexify_hermitian B.prop⟩

@[simp] lemma realHermitianComplexify_coe (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    (realHermitianComplexify B : Matrix (Fin N) (Fin N) ℂ) = complexify B := rfl

lemma realHermitianComplexify_continuous : Continuous (realHermitianComplexify (N := N)) :=
  (complexifyCLM.continuous.comp continuous_subtype_val).subtype_mk _

lemma matrixField_eq_realPart {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    matrixField σ δ k B = realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := by
  rw [← complexify_matrixField hσ hδ k hB, realPartCLM_complexify]

lemma matrixField_continuous {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) :
    Continuous (fun B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) ↦ matrixField σ δ k B) := by
  have hc := (hermitianField_locallyLipschitz hσ hδ
    (complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2)))).continuous
  have hh := realPartCLM.continuous.comp (hc.comp realHermitianComplexify_continuous)
  convert! hh using 1
  funext B
  exact matrixField_eq_realPart hσ hδ k B.prop

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
