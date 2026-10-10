import Mathlib
import OAI.Analysis.Crouzeix.HolomorphicAlgebra
import OAI.Analysis.Crouzeix.PhysicalProjection

namespace OAI

/-! Physical Module. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma realCLM_eq_of_matrixLaurent {k : ℕ} {L R : BoundaryL2 k →L[ℝ] BoundaryL2 k}
    (h : ∀ a c, L (boundaryField (matrixLaurentMonomial a c)) =
      R (boundaryField (matrixLaurentMonomial a c))) : L = R := by
  have ha : L.adjoint = R.adjoint := by
    apply ContinuousLinearMap.ext
    intro v
    apply eq_of_inner_matrixLaurentMonomial
    intro a c
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, h]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    congrArg (fun T : BoundaryL2 k →L[ℝ] BoundaryL2 k => T.adjoint) ha

lemma lpLeft_boundaryField {k : ℕ} (F V : C(CircleSpace, Coeff k))
    (hF : ∀ t, ‖F t‖ ≤ 1) :
    lpLeft F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
      (boundaryField V) = boundaryField (F*V) := by
  apply Lp.ext
  filter_upwards [lpLeft_apply_ae F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
    (boundaryField V), boundaryField_apply_ae V, boundaryField_apply_ae (F*V)] with t ht hv hfv
  rw [ht, hv, hfv, ofHS_toHS]
  rfl

lemma lpRight_boundaryField {k : ℕ} (F V : C(CircleSpace, Coeff k))
    (hF : ∀ t, ‖F t‖ ≤ 1) :
    lpRight F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
      (boundaryField V) = boundaryField (V*F) := by
  apply Lp.ext
  filter_upwards [lpRight_apply_ae F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)
    (boundaryField V), boundaryField_apply_ae V, boundaryField_apply_ae (V*F)] with t ht hv hfv
  rw [ht, hv, hfv, ofHS_toHS]
  rfl

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

def analyticTrace {V : Set ℂ} (hUV : closure U ⊆ V) (f : ℂ → ℂ)
    (hf : ContinuousOn f V) : C(CircleSpace, ℂ) :=
  ⟨fun t => f (C.boundaryMap t), hf.comp_continuous C.boundaryMap.continuous
    (fun t => hUV (C.boundaryMap_mem_frontier t).1)⟩

lemma boundaryCauchy_polynomialTrace (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (p : Polynomial ℂ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l
        (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn))) =
      boundaryField (scalarChannel i l
        (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn)) := by
  have he : scalarChannel i l
      (C.analyticTrace (subset_univ _) p.eval p.continuous.continuousOn) =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • scalarChannel i l (C.boundaryMap^j) := by
    ext t a b
    simp only [analyticTrace, scalarChannel, ContinuousMap.coe_mk, ContinuousMap.sum_apply,
      Matrix.sum_apply, ContinuousMap.smul_apply, Matrix.smul_apply, ContinuousMap.pow_apply,
      Polynomial.eval_eq_sum_range, Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [he, boundaryField_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [boundaryField_smul, C.boundaryCauchy_complex_smul, C.boundaryCauchy_physical_power hU hc]

lemma boundaryCauchy_analyticTrace (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V) {k : ℕ} (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (C.analyticTrace hUV f hf.continuousOn))) =
      boundaryField (scalarChannel i l (C.analyticTrace hUV f hf.continuousOn)) := by
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hb.isCompact_closure hc.closure hV hUV hf
  let Fn (n : ℕ) := scalarChannel i l
    (C.analyticTrace (subset_univ _) (p n).eval (p n).continuous.continuousOn)
  let F := scalarChannel i l (C.analyticTrace hUV f hf.continuousOn)
  have ht : Tendsto Fn atTop (𝓝 F) := by
    have hs : TendstoUniformly (fun n t => (p n).eval (C.boundaryMap t))
        (fun t => f (C.boundaryMap t)) atTop := by
      have he : C.boundaryMap ⁻¹' closure U = univ :=
        eq_univ_of_forall (fun t => (C.boundaryMap_mem_frontier t).1)
      simpa only [he, tendstoUniformlyOn_univ, Function.comp_def] using
        hp.comp C.boundaryMap
    have hct : Tendsto (fun n => C.analyticTrace (subset_univ _) (p n).eval
        (p n).continuous.continuousOn) atTop (𝓝 (C.analyticTrace hUV f hf.continuousOn)) :=
      ContinuousMap.tendsto_iff_tendstoUniformly.mpr hs
    let T : ℂ →L[ℂ] Coeff k := (ContinuousLinearMap.id ℂ ℂ).smulRight (Matrix.single i l 1)
    exact ((ContinuousLinearMap.compLeftContinuous ℂ CircleSpace T).continuous.tendsto _).comp hct
  have hlt := ((boundaryFieldCLM k).continuous.tendsto F).comp ht
  have hrt := (boundaryCauchy (C.boundaryOperator hc k)).continuous.tendsto _ |>.comp hlt
  have heq : ∀ n, boundaryCauchy (C.boundaryOperator hc k) (boundaryFieldCLM k (Fn n)) =
      boundaryFieldCLM k (Fn n) := fun n => C.boundaryCauchy_polynomialTrace hU hc (p n) i l
  simp only [Function.comp_def, heq] at hrt
  exact tendsto_nhds_unique hrt hlt

def matrixAnalyticTrace {V : Set ℂ} (hUV : closure U ⊆ V) {k : ℕ} (f : ℂ → Coeff k)
    (hf : ContinuousOn f V) : C(CircleSpace, Coeff k) :=
  ⟨fun t => f (C.boundaryMap t), hf.comp_continuous C.boundaryMap.continuous
    (fun t => hUV (C.boundaryMap_mem_frontier t).1)⟩

lemma boundaryCauchy_matrixAnalyticTrace (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn)) =
      boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) := by
  classical
  have he : C.matrixAnalyticTrace hUV f hf.continuousOn =
      ∑ i : Fin k, ∑ l : Fin k,
        scalarChannel i l (C.analyticTrace hUV (fun z => f z i l) (hf i l).continuousOn) := by
    ext t a b
    simp only [matrixAnalyticTrace, scalarChannel, analyticTrace, ContinuousMap.coe_mk,
      ContinuousMap.sum_apply, Matrix.smul_single, smul_eq_mul, mul_one]
    exact congrArg (fun M : Coeff k => M a b) (Matrix.matrix_eq_sum_single (f (C.boundaryMap t)))
  rw [he, boundaryField_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [boundaryField_sum, map_sum]
  exact Finset.sum_congr rfl (fun l _ => C.boundaryCauchy_analyticTrace hU hc hb hV hUV (hf i l) i l)

def physicalRepresentative {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) (z : ℂ) : Coeff k :=
  (c * C.physicalCoefficient a.1 z) • Matrix.single a.2.1 a.2.2 1

lemma physicalRepresentative_holomorphic {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    EntrywiseHolomorphic C.outerDomain (C.physicalRepresentative a c) := by
  intro i j
  exact ((C.differentiableOn_physicalCoefficient a.1).const_mul c).mul_const _

lemma physicalRepresentative_trace {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    C.matrixAnalyticTrace C.closure_subset_outerDomain (C.physicalRepresentative a c)
      (C.physicalRepresentative_holomorphic a c).continuousOn = c • C.physicalChannel a := by
  ext t i j
  simp only [matrixAnalyticTrace, physicalRepresentative, physicalChannel, scalarChannel,
    ContinuousMap.coe_mk, ContinuousMap.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

lemma boundaryCauchy_left_module (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f)
    (hF : ∀ t, ‖C.matrixAnalyticTrace hUV f hf.continuousOn t‖ ≤ 1) :
    let F := C.matrixAnalyticTrace hUV f hf.continuousOn
    let M := C.boundaryOperator hc k
    (boundaryCauchy M).comp ((lpLeft F F.continuous.aestronglyMeasurable
      (Eventually.of_forall hF)).comp (boundaryCauchy M)) =
    (lpLeft F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)).comp (boundaryCauchy M) := by
  dsimp only
  apply realCLM_eq_of_matrixLaurent
  intro a c
  simp only [ContinuousLinearMap.comp_apply, C.boundaryCauchy_matrixLaurentMonomial hU hc]
  rw [lpLeft_boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) (c • C.physicalChannel a) hF]
  let W := V ∩ C.outerDomain
  have hw : closure U ⊆ W := fun z hz => ⟨hUV hz, C.closure_subset_outerDomain hz⟩
  have hprod : EntrywiseHolomorphic W (fun z => f z * C.physicalRepresentative a c z) := by
    intro i j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro l _
    exact ((hf i l).mono inter_subset_left).fun_mul
      ((C.physicalRepresentative_holomorphic a c l j).mono inter_subset_right)
  have he : C.matrixAnalyticTrace hUV f hf.continuousOn * (c • C.physicalChannel a) =
      C.matrixAnalyticTrace hw (fun z => f z * C.physicalRepresentative a c z) hprod.continuousOn := by
    rw [← C.physicalRepresentative_trace]
    rfl
  rw [he]
  exact C.boundaryCauchy_matrixAnalyticTrace hU hc hb (hV.inter C.isOpen_outerDomain) hw hprod

lemma boundaryCauchy_right_module (hU : IsOpen U) (hc : Convex ℝ U)
    (hb : Bornology.IsBounded U) {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {k : ℕ} {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic V f)
    (hF : ∀ t, ‖C.matrixAnalyticTrace hUV f hf.continuousOn t‖ ≤ 1) :
    let F := C.matrixAnalyticTrace hUV f hf.continuousOn
    let M := C.boundaryOperator hc k
    (boundaryCauchy M).comp ((lpRight F F.continuous.aestronglyMeasurable
      (Eventually.of_forall hF)).comp (boundaryCauchy M)) =
    (lpRight F F.continuous.aestronglyMeasurable (Eventually.of_forall hF)).comp (boundaryCauchy M) := by
  dsimp only
  apply realCLM_eq_of_matrixLaurent
  intro a c
  simp only [ContinuousLinearMap.comp_apply, C.boundaryCauchy_matrixLaurentMonomial hU hc]
  rw [lpRight_boundaryField (C.matrixAnalyticTrace hUV f hf.continuousOn) (c • C.physicalChannel a) hF]
  let W := V ∩ C.outerDomain
  have hw : closure U ⊆ W := fun z hz => ⟨hUV hz, C.closure_subset_outerDomain hz⟩
  have hprod : EntrywiseHolomorphic W (fun z => C.physicalRepresentative a c z * f z) := by
    intro i j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro l _
    exact ((C.physicalRepresentative_holomorphic a c i l).mono inter_subset_right).fun_mul
      ((hf l j).mono inter_subset_left)
  have he : (c • C.physicalChannel a) * C.matrixAnalyticTrace hUV f hf.continuousOn =
      C.matrixAnalyticTrace hw (fun z => C.physicalRepresentative a c z * f z) hprod.continuousOn := by
    rw [← C.physicalRepresentative_trace]
    rfl
  rw [he]
  exact C.boundaryCauchy_matrixAnalyticTrace hU hc hb (hV.inter C.isOpen_outerDomain) hw hprod

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
