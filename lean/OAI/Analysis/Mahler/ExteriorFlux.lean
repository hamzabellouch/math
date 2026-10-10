import OAI.Analysis.Mahler.HomogeneousFlux
import OAI.Analysis.Mahler.HolomorphicRegularity
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Multiplication by i as a real continuous linear map. -/
noncomputable def complexStructure : E →L[ℝ] E :=
  (I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] lemma complexStructure_apply (v : E) : complexStructure v = I • v := rfl

/-- The operator d^c, bundled as a real continuous linear one-form. -/
noncomputable def dcLinear (u : E → ℂ) (x : E) : E →L[ℝ] ℂ :=
  (-1 / 4 : ℂ) • (fderiv ℝ u x).comp complexStructure

@[simp] lemma dcLinear_apply (u : E → ℂ) (x v : E) : dcLinear u x v = dc u x v := by
  simp [dcLinear, dc]
  ring

/-- A continuous linear one-form regarded as a continuous alternating one-form. -/
noncomputable def oneForm (a : E → E →L[ℝ] ℂ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ 0 (a x)

omit normedSpaceComplexE isScalarTowerRealComplexE in
@[simp] lemma oneForm_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a : E → E →L[ℝ] ℂ) (x : E) (v : Fin 1 → E) :
    oneForm a x v = a x (v 0) := rfl

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma differentiableAt_oneForm [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x ha

/-- Exterior differentiation uses the usual unnormalized alternating sum. -/
lemma extDeriv_oneForm {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    extDeriv (oneForm a) x ![v, w] =
      fderiv ℝ (fun y => a y w) x v - fderiv ℝ (fun y => a y v) x w := by
  rw [extDeriv_apply (differentiableAt_oneForm ha)]
  simp [Fin.sum_univ_two, Fin.removeNth, oneForm_apply, sub_eq_add_neg]

lemma hasDerivAt_circle_smul (point : E) :
    HasDerivAt (fun angle : ℝ => circleMap 0 1 angle • point) (I • point) 0 := by
  simpa [circleMap] using (hasDerivAt_circleMap 0 1 0).smul_const point

lemma hasDerivAt_circle_form {form : E → E →L[ℝ] ℂ} {point : E}
    (hform : DifferentiableAt ℝ form point) (argument : E) :
    HasDerivAt
      (fun angle : ℝ => form (circleMap 0 1 angle • point)
        (circleMap 0 1 angle • argument))
      (form point (I • argument) + fderiv ℝ form point (I • point) argument) 0 := by
  have hzero : circleMap 0 1 0 = 1 := by simp [circleMap]
  have hbase : HasFDerivAt form (fderiv ℝ form point) (circleMap 0 1 0 • point) := by
    simpa only [hzero, one_smul] using hform.hasFDerivAt
  have hcomposition : HasDerivAt (fun angle : ℝ => form (circleMap 0 1 angle • point))
      (fderiv ℝ form point (I • point)) 0 :=
    hbase.comp_hasDerivAt 0 (hasDerivAt_circle_smul point)
  simpa only [hzero, one_smul, add_comm] using
    hcomposition.clm_apply (hasDerivAt_circle_smul argument)

lemma fderiv_circle_invariant {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x)
    (hinv : ∀ (t : ℝ) (w : E),
      a (circleMap 0 1 t • x) (circleMap 0 1 t • w) = a x w) (w : E) :
    a x (I • w) + fderiv ℝ a x (I • x) w = 0 := by
  have h1 := hasDerivAt_circle_form ha w
  have he : (fun t : ℝ => a (circleMap 0 1 t • x) (circleMap 0 1 t • w)) =
      (fun _ => a x w) := funext (fun t => hinv t w)
  rw [he] at h1
  exact h1.unique (hasDerivAt_const 0 (a x w))

lemma fderiv_circle_contraction {a : E → E →L[ℝ] ℂ} {x : E} {q : ℂ}
    (ha : DifferentiableAt ℝ a x)
    (hconst : (fun y => a y (I • y)) =ᶠ[𝓝 x] (fun _ => q)) (w : E) :
    a x (I • w) + fderiv ℝ a x w (I • x) = 0 := by
  have h2 := ha.hasFDerivAt.clm_apply complexStructure.hasFDerivAt
  change HasFDerivAt (fun y => a y (I • y)) _ x at h2
  have hi2 := congrArg (fun L : E →L[ℝ] ℂ => L w)
    (h2.fderiv.symm.trans hconst.fderiv_eq)
  simpa using hi2

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma fderiv_form_apply {form : E → E →L[ℝ] ℂ} {point : E}
    (hform : DifferentiableAt ℝ form point) (argument direction : E) :
    fderiv ℝ (fun value => form value argument) point direction =
      fderiv ℝ form point direction argument := by
  simpa using congrArg (fun derivative : E →L[ℝ] ℂ => derivative direction)
    (hform.hasFDerivAt.clm_apply (hasFDerivAt_const argument point)).fderiv

/-- Cartan's contraction identity for the circle field, proved using actual
Fréchet derivatives and circle invariance. -/
theorem extDeriv_circle_horizontal {a : E → E →L[ℝ] ℂ} {x : E} {q : ℂ}
    (ha : DifferentiableAt ℝ a x)
    (hinv : ∀ (t : ℝ) (w : E),
      a (circleMap 0 1 t • x) (circleMap 0 1 t • w) = a x w)
    (hconst : (fun y => a y (I • y)) =ᶠ[𝓝 x] (fun _ => q)) (w : E) :
    extDeriv (oneForm a) x ![I • x, w] = 0 := by
  rw [extDeriv_oneForm ha, fderiv_form_apply ha, fderiv_form_apply ha]
  linear_combination fderiv_circle_invariant ha hinv w -
    fderiv_circle_contraction ha hconst w

/-- C^2 regularity of log tau follows from first-order holomorphicity. -/
lemma contDiffAt_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) : ContDiffAt ℝ 2 (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ 2 (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := 2) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

/-- d^c respects the circle action when the scalar function does. -/
lemma dcLinear_rotation {u : E → ℂ} {x : E} {c : ℂ}
    (hu : DifferentiableAt ℝ u (c • x))
    (hinv : ∀ y, u (c • y) = u y) (w : E) :
    dcLinear u (c • x) (c • w) = dcLinear u x w := by
  let L : E →L[ℝ] E := (c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have h := hu.hasFDerivAt.comp x L.hasFDerivAt
  have he : (u ∘ L) = u := funext hinv
  change HasFDerivAt (u ∘ L) _ x at h
  rw [he] at h
  have hd := congrArg (fun A : E →L[ℝ] ℂ => A (I • w)) h.fderiv
  simp only [ContinuousLinearMap.comp_apply] at hd
  have hm : L (I • w) = I • (c • w) := by simp [L, smul_smul, mul_comm]
  rw [hm] at hd
  simp only [dcLinear_apply, dc]
  rw [hd]

variable {ι : Type*} [Fintype ι]
/-- The homogeneous alpha has horizontal exterior derivative, with all
regularity derived from holomorphicity. -/
theorem homogeneous_extDeriv_horizontal [FiniteDimensional ℂ E]
    {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (ht : 0 < tau f x)
    (hh : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y) (w : E) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![I • x, w] = 0 := by
  have hc := contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ x)
    (fun j => (hf j).differentiableOn) ht
  apply extDeriv_circle_horizontal (q := (m : ℂ) / 2) (differentiableAt_dcLinear hc)
  · intro t v
    have hnorm : normSq (circleMap 0 1 t) = 1 := by
      rw [Complex.normSq_eq_norm_sq]
      simp
    apply dcLinear_rotation
    · apply differentiable_logTau (fun j => (hf j).differentiableAt)
      simpa [tau_homogeneous (fun j c => hh j x c), hnorm] using ht
    · intro y
      exact logTau_circle_invariant (fun j c => hh j y c) hnorm
  · have hcont : ContinuousAt (tau f) x := by
      have h := Complex.continuous_re.continuousAt.comp
        (differentiable_energy (x := x) (fun j => (hf j).differentiableAt)).continuousAt
      simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h
    filter_upwards [hcont.eventually (lt_mem_nhds ht)] with y hy
    simp only [dcLinear_apply]
    exact homogeneous_dc_circle (fun j => (hf j).differentiableAt) hy (fun j c => hh j y c)

end Mahler

end OAI
