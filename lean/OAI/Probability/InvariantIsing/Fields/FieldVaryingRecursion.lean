import OAI.Probability.InvariantIsing.Fields.FieldGaussianContinuity
import OAI.Probability.InvariantIsing.Fields.FieldCapEstimate
import OAI.Probability.InvariantIsing.Fields.FieldScalarChain

namespace OAI

/-! Fixed finite cascade exponents with varying nonnegative scalar
variances. These are the actual log-cosh recursion and spin observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVaryingValue {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) : ℝ → ℝ :=
  L.foldr (fun av F => gaussianOperator av.1 (av.2 t) F) (fun z => Real.log (Real.cosh z))

def fieldVaryingMean {E : Type*} : List (ℝ × (E → ℝ≥0)) → E → ℝ → ℝ
  | [], _ => Real.tanh
  | av :: L, t => fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
      (fieldVaryingMean L t)

def fieldVaryingSquares {E : Type*} : (L : List (ℝ × (E → ℝ≥0))) → E →
    Fin (L.length + 1) → ℝ → ℝ
  | [], _ => fun _ z => (Real.tanh z) ^ 2
  | av :: L, t => Fin.cons (fun z => (fieldVaryingMean (av :: L) t z) ^ 2)
      (fun i => fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
        (fieldVaryingSquares L t i))

lemma fieldVaryingValue_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) :
    fieldVaryingValue L t = fieldScalarValue (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) := by
  simp only [fieldVaryingValue, fieldScalarValue, List.foldr_map]

lemma fieldVaryingMean_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (t : E) :
    fieldVaryingMean L t = fieldScalarMean (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    simp only [fieldVaryingMean, List.map_cons, fieldScalarMean,
      fieldVaryingValue_eq_scalar, ih]

lemma fieldVaryingSquares_eq_scalar {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (t : E) (i : Fin (L.length + 1)) :
    fieldVaryingSquares L t i = fieldScalarSquares (L.map (fun av => (av.1, av.2 t)))
      (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) i) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [fieldVaryingSquares, Fin.cons_zero, Fin.cast_zero]
      funext z
      rw [fieldScalarSquares_zero, fieldVaryingMean_eq_scalar]
    · change fieldSpinTransition av.1 (av.2 t) (fieldVaryingValue L t)
        (fieldVaryingSquares L t j) =
          fieldSpinTransition av.1 (av.2 t)
            (fieldScalarValue (L.map (fun bv => (bv.1, bv.2 t)))
              (fun z => Real.log (Real.cosh z)))
            (fieldScalarSquares (L.map (fun bv => (bv.1, bv.2 t)))
              (fun z => Real.log (Real.cosh z)) Real.tanh (Fin.cast (by simp) j))
      rw [fieldVaryingValue_eq_scalar, ih]

lemma fieldVaryingValue_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) :
    Measurable (fieldVaryingValue L t) ∧ HasLinearGrowth (fieldVaryingValue L t) := by
  rw [fieldVaryingValue_eq_scalar]
  apply fieldScalarValue_regular _ _ measurable_logCosh logCosh_linearGrowth
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingMean_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) :
    Measurable (fieldVaryingMean L t) ∧ ∀ z, |fieldVaryingMean L t z| ≤ 1 := by
  rw [fieldVaryingMean_eq_scalar]
  apply fieldScalarMean_regular (a := Real.tanh) _ _ measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun z : ℝ => Real.tanh z); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingSquares_regular {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (i : Fin (L.length + 1)) :
    Measurable (fieldVaryingSquares L t i) ∧
      ∀ z, fieldVaryingSquares L t i z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fieldVaryingSquares_eq_scalar]
  apply fieldScalarSquares_regular (a := Real.tanh) _ _ measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun z : ℝ => Real.tanh z); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one
  intro av hav
  obtain ⟨bv, hbv, rfl⟩ := List.mem_map.mp hav
  exact hL bv hbv

lemma fieldVaryingValue_nonneg {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) (t : E) (z : ℝ) :
    0 ≤ fieldVaryingValue L t z := by
  induction L generalizing z with
  | nil => exact Real.log_nonneg (Real.one_le_cosh z)
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldVaryingValue_regular L ht t
    have hg : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) := by
      refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
      simp
    have hm := gaussianOperator_mono measurable_const hr.1 hg hr.2
      (fun y => ih ht y) (hL av List.mem_cons_self).le (av.2 t) z
    simpa only [fieldVaryingValue, List.foldr_cons, gaussianOperator, ite_self,
      mul_zero, Real.exp_zero, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul, Real.log_one, mul_zero] using hm

def fieldVaryingCap {E : Type*} (L : List (ℝ × (E → ℝ≥0))) (V : ℝ) : ℝ :=
  (L.map (fun av => av.1 * V / 2 + Real.log 2 / av.1)).sum

lemma fieldVaryingValue_bound {E : Type*} (L : List (ℝ × (E → ℝ≥0)))
    (hL : ∀ av ∈ L, 0 < av.1) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ av ∈ L, ∀ t, (av.2 t : ℝ) ≤ V) :
    0 ≤ fieldVaryingCap L V ∧
      ∀ t z, |fieldVaryingValue L t z| ≤ fieldVaryingCap L V + |z| := by
  induction L with
  | nil =>
    refine ⟨le_rfl, fun t z => ?_⟩
    simpa only [fieldVaryingValue, fieldVaryingCap, List.map_nil, List.sum_nil,
      List.foldr_nil, zero_add] using abs_log_cosh_le z
  | cons av L ih =>
    have ht : ∀ bv ∈ L, 0 < bv.1 := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hvt := fun bv hb t => hv bv (List.mem_cons_of_mem av hb) t
    obtain ⟨hc, hb⟩ := ih ht hvt
    have ha := hL av List.mem_cons_self
    have hav := hv av List.mem_cons_self
    have hcap : 0 ≤ fieldVaryingCap (av :: L) V := by
      change 0 ≤ (av.1 * V / 2 + Real.log 2 / av.1) + fieldVaryingCap L V
      positivity
    refine ⟨hcap, fun t z => ?_⟩
    have hr := fieldVaryingValue_regular L ht t
    have hg := linearGrowth_const_add abs_linearGrowth (fieldVaryingCap L V)
    have hm := gaussianOperator_mono (G := fun y : ℝ => fieldVaryingCap L V + |y|)
      hr.1 (by fun_prop)
      hr.2 hg (fun y => (le_abs_self _).trans (hb t y)) ha.le (av.2 t) z
    rw [gaussianOperator_const_add (F := fun y : ℝ => |y|)
      (by fun_prop) abs_linearGrowth] at hm
    have habs : gaussianOperator av.1 (av.2 t) (fun y : ℝ => |y|) z ≤
        |z| + av.1 * (av.2 t : ℝ) / 2 + Real.log 2 / av.1 := by
      rw [gaussianOperator_eq_transform]
      exact gaussianTransform_abs_bound (av.2 t).coe_nonneg ha z
    rw [abs_of_nonneg (fieldVaryingValue_nonneg (av :: L) hL t z)]
    change gaussianOperator av.1 (av.2 t) (fieldVaryingValue L t) z ≤ _
    have hvar := mul_le_mul_of_nonneg_left (hav t) ha.le
    change _ ≤ (av.1 * V / 2 + Real.log 2 / av.1) + fieldVaryingCap L V + |z|
    linarith

end InvariantIsing

end

end OAI
