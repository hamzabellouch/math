import OAI.Probability.InvariantIsing.Core.Variational

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

/-- Gaussian logarithmic integration, with ordinary expectation at exponent zero. -/
def gaussianOperator (a v : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  if a = 0 then ∫ g, f (z + Real.sqrt v * g) ∂gaussianReal 0 1
  else a⁻¹ * Real.log (∫ g, Real.exp (a * f (z + Real.sqrt v * g)) ∂gaussianReal 0 1)

@[simp] lemma gaussianOperator_zero_variance (a : ℝ) (f : ℝ → ℝ) :
    gaussianOperator a 0 f = f := by
  funext z
  by_cases ha : a = 0
  · simp [gaussianOperator, ha]
  · simp [gaussianOperator, ha]

/-- Positive intervals partitioning the unit interval, with monotone covariance heights. -/
structure FieldStep where
  depth : ℕ
  cut : Fin (depth + 2) → ℝ
  ordered_cut : StrictMono cut
  first : cut 0 = 0
  last : cut (Fin.last (depth + 1)) = 1
  height : Fin (depth + 1) → ℝ
  nonneg : ∀ i, 0 ≤ height i
  ordered_height : Monotone height

/-- A finite covariance step path, with arbitrary values assigned at its cuts. -/
def fieldFunction (h : FieldStep) (s : ℝ) : ℝ :=
  ∑ i : Fin (h.depth + 1),
    if h.cut i.castSucc < s ∧ s < h.cut i.succ then h.height i else 0

/-- Exponent and covariance increment for one backward step. -/
def fieldIncrement (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ × ℝ :=
  (h.cut i.castSucc, h.height i -
    if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩)

/-- The canonical one-site value at initial bias `b`, with the diagonal covariance subtraction. -/
def fieldValue (h : FieldStep) (b : ℝ) : ℝ :=
  ((List.ofFn (fieldIncrement h)).foldr
    (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z))) b -
    h.height (Fin.last h.depth) / 2

/-- The field-order-parameter pairing on `(0,1)`. -/
def fieldPairing (p : OverlapPath) (h : FieldStep) : ℝ :=
  ∫ s, p s * fieldFunction h s ∂pathMeasure

/-- Equation (1.6). Infinite suprema are retained as extended real values. -/
def entropyFunctional (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)

/-- Equation (1.7) at temperature parameter one. -/
def spectralFunctional (R : ℝ → ℝ) (p : OverlapPath) : ℝ :=
  (1 / 2 : ℝ) * ∫ r, R (deficit p r) ∂pathMeasure

/-- Equation (1.8), with the infimum outside the field supremum. -/
def variationalFunctional (R : ℝ → ℝ) : EReal :=
  ⨅ p : OverlapPath, entropyFunctional p + (spectralFunctional R p : EReal)

/-- The admissible zero covariance field. -/
def zeroField : FieldStep where
  depth := 0
  cut := fun i => i.val
  ordered_cut := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  first := by norm_num
  last := by norm_num
  height := fun _ => 0
  nonneg := fun _ => le_rfl
  ordered_height := monotone_const

@[simp] lemma fieldFunction_zero : fieldFunction zeroField = fun _ => 0 := by
  funext s
  simp [fieldFunction, zeroField]

@[simp] lemma fieldValue_zero (b : ℝ) : fieldValue zeroField b = Real.log (Real.cosh b) := by
  simp [fieldValue, zeroField, fieldIncrement, List.ofFn_succ]

@[simp] lemma fieldPairing_zero (p : OverlapPath) : fieldPairing p zeroField = 0 := by
  simp [fieldPairing]

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma fieldFunction_nonneg (h : FieldStep) (s : ℝ) : 0 ≤ fieldFunction h s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact h.nonneg i
  · exact le_rfl

lemma spectralFunctional_constant (a : ℝ) (p : OverlapPath) :
    spectralFunctional (fun _ => a) p = a / 2 := by
  simp [spectralFunctional]
  ring

lemma integrable_spectral_composition (R : ℝ → ℝ) (hR : Continuous R)
    (p : OverlapPath) : Integrable (fun r => R (deficit p r)) pathMeasure := by
  change IntegrableOn (fun r => R (deficit p r)) (Set.Ioo (0 : ℝ) 1)
  exact ((hR.comp (continuous_deficit p)).continuousOn.integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- Section 6's uniform comparison of spectral functionals. -/
lemma abs_spectralFunctional_sub_le (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) (p : OverlapPath) :
    |spectralFunctional R p - spectralFunctional Q p| ≤ δ / 2 := by
  have hr : ∀ᵐ r ∂pathMeasure, r ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hi := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun r => R (deficit p r) - Q (deficit p r)) (C := δ) (by
      filter_upwards [hr] with r hr
      simpa only [Real.norm_eq_abs] using hδ _ (deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩))
  have hib : |∫ r, R (deficit p r) - Q (deficit p r) ∂pathMeasure| ≤ δ := by
    simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
      ENNReal.toReal_one, mul_one] using hi
  rw [spectralFunctional, spectralFunctional, ← mul_sub,
    ← integral_sub (integrable_spectral_composition R hR p)
      (integrable_spectral_composition Q hQ p), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * δ := mul_le_mul_of_nonneg_left hib (by norm_num)
    _ = δ / 2 := by ring

/-- A common uniform spectral error passes through the path infimum without
exchanging the field supremum and the path infimum. -/
lemma variationalFunctional_le_add (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) :
    variationalFunctional R ≤ variationalFunctional Q + ((δ / 2 : ℝ) : EReal) := by
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mp
  apply le_iInf
  intro p
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mpr
  have hspec : (spectralFunctional R p : EReal) ≤
      (spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe
    have hb := (abs_le.mp (abs_spectralFunctional_sub_le R Q hR hQ δ hδ p)).2
    linarith
  calc
    variationalFunctional R ≤ entropyFunctional p + (spectralFunctional R p : EReal) :=
      iInf_le _ p
    _ ≤ entropyFunctional p +
        ((spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal)) :=
      add_le_add le_rfl hspec
    _ = _ := by rw [add_assoc]

end InvariantIsing

end

end OAI
