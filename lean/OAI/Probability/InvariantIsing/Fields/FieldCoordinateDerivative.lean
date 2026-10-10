import OAI.Probability.InvariantIsing.Fields.FieldScalarComposition
import OAI.Probability.InvariantIsing.Fields.FieldTerminalOrder

namespace OAI

/-! Exact single-height derivatives of the finite Gaussian field value.
An interior height changes its two adjacent covariance increments with
opposite signs. The final height includes the diagonal subtraction. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldFixedAffine (S : List (ℝ × ℝ≥0)) : List FieldAffineStep :=
  S.map fun av => ⟨av.2, 0, av.1⟩

lemma fieldFixedAffine_base (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) :
    ∀ av ∈ fieldFixedAffine S, 0 < av.base := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hS bv hb

lemma fieldFixedAffine_slope (S : List (ℝ × ℝ≥0)) :
    ∀ av ∈ fieldFixedAffine S, av.slope = 0 := by
  intro av hav
  obtain ⟨bv, _, rfl⟩ := List.mem_map.mp hav
  rfl

lemma fieldFixedAffine_increments (S : List (ℝ × ℝ≥0)) (t : ℝ) :
    fieldAffineIncrements (fieldFixedAffine S) t = S := by
  simp only [fieldAffineIncrements, fieldFixedAffine, List.map_map, Function.comp_def]
  have he : (fun av : ℝ × ℝ≥0 =>
      (((⟨av.2, 0, av.1⟩ : FieldAffineStep).exponent),
        Real.toNNReal ((⟨av.2, 0, av.1⟩ : FieldAffineStep).base +
          (⟨av.2, 0, av.1⟩ : FieldAffineStep).slope * t))) = id := by
    funext av
    simp
  rw [he, List.map_id]

/-- Actual increment list when a single nonterminal height is varied. -/
def fieldAdjacentIncrements (P S : List (ℝ × ℝ≥0)) (a b ζ η t : ℝ) :
    List (ℝ × ℝ≥0) :=
  P ++ (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S

def fieldAdjacentLevel (P S : List (ℝ × ℝ≥0)) (a b ζ η t : ℝ) :
    Fin ((fieldAdjacentIncrements P S a b ζ η t).length + 1) :=
  fieldAppendIndex P ((ζ, Real.toNNReal (a + t)) ::
    (η, Real.toNNReal (b - t)) :: S) 1

private lemma adjacent_value (a b ζ η : ℝ) (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldAdjacentFamily a b ζ η (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) =
    fieldScalarValue ((ζ, Real.toNNReal (a + t)) ::
      (η, Real.toNNReal (b - t)) :: S) (fun z => Real.log (Real.cosh z)) := by
  change gaussianTransform (a + 1 * t) ζ
    (fun y => gaussianTransform (b + -1 * t) η
      (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
        (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) y) = _
  rw [one_mul, neg_one_mul, ← sub_eq_add_neg, field_gaussianTransform_eq_operator]
  have he : (fun y => gaussianTransform (b - t) η
      (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
        (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) y) =
      gaussianOperator η (Real.toNNReal (b - t))
        (fieldScalarValue S (fun z => Real.log (Real.cosh z))) := by
    rw [field_gaussianTransform_eq_operator]
    rw [show (fun z => (fieldAdjacentTail a b (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).U (t, z)) =
      (fun z => fieldAffineValue (fieldFixedAffine S) (t, z)) from
      congrArg (fun f => fun z => f (t, z))
        (fieldAffineFamily_value _ _ _ _),
      fieldAffineValue_scalar, fieldFixedAffine_increments]
  rw [he]
  rfl

private lemma adjacent_inner_mean (a b η : ℝ) (S : List (ℝ × ℝ≥0))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldAdjacentInner a b η (fieldFixedAffine S)
      (fieldFixedAffine_base S hS) (fieldFixedAffine_slope S)).X (t, z)) =
    fieldScalarMean ((η, Real.toNNReal (b - t)) :: S)
      (fun z => Real.log (Real.cosh z)) Real.tanh := by
  let av : FieldAffineStep := ⟨b, -1, η⟩
  have hv : ∀ v ∈ av :: fieldFixedAffine S, ∀ q ∈ Ioo (-a) b,
      0 < v.base + v.slope * q := by
    intro v hv q hq
    rcases List.mem_cons.mp hv with rfl | hv
    · dsimp only [av]
      linarith [hq.2]
    · rw [fieldFixedAffine_slope S v hv, zero_mul, add_zero]
      exact fieldFixedAffine_base S hS v hv
  have h := fieldAffineFamily_mean (Ioo (-a) b) isOpen_Ioo
    (av :: fieldFixedAffine S) hv t
  change (fun z => (fieldAffineFamily (Ioo (-a) b) isOpen_Ioo
    (av :: fieldFixedAffine S) hv).X (t, z)) = _
  rw [h]
  simp only [fieldAffineIncrements, List.map_cons]
  rw [← fieldAffineIncrements, fieldFixedAffine_increments]
  simp only [av, neg_one_mul, ← sub_eq_add_neg]

/-- The manuscript's finite interior-height gradient before the fixed
normalizing diagonal term. The derivative is minus half the cell width
multiplied by its actual conditional squared spin mean. -/
theorem hasDerivAt_fieldAdjacentValue
    (P S : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < (av.2 : ℝ))
    (hS : ∀ av ∈ S, 0 < (av.2 : ℝ))
    (a b ζ η t z : ℝ) (ht : t ∈ Ioo (-a) b) :
    HasDerivAt (fun q => fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
      (fun y => Real.log (Real.cosh y)) z)
      (-(η - ζ) / 2 * fieldScalarSquares (fieldAdjacentIncrements P S a b ζ η t)
        (fun y => Real.log (Real.cosh y)) Real.tanh
        (fieldAdjacentLevel P S a b ζ η t) z) t := by
  let L := fieldFixedAffine S
  let hb := fieldFixedAffine_base S hS
  let hs := fieldFixedAffine_slope S
  let F := fieldAdjacentTail a b L hb hs
  let G := fieldAdjacentInner a b η L hb hs
  let H := fieldAdjacentFamily a b ζ η L hb hs
  let K := fieldConstantPrefix isOpen_Ioo H P hP
  have hval (q : ℝ) : (fun y => K.U (q, y)) =
      fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
        (fun y => Real.log (Real.cosh y)) := by
    rw [show (fun y => K.U (q, y)) =
      fieldScalarValue P (fun y => H.U (q, y)) from
        fieldConstantPrefix_value isOpen_Ioo H P hP q,
      adjacent_value a b ζ η S hS q]
    exact (fieldScalarValue_append P _ _).symm
  have htan : (fun y => H.T (t, y)) = fun y =>
      -(η - ζ) / 2 * gaussianTiltAverage (a + t) ζ
        (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) y := by
    funext y
    exact F.adjacent_tangent isOpen_Ioo a b ζ η
      (fun q hq => by linarith [hq.1]) (fun q hq => by linarith [hq.2])
      (p := (t, y)) ht (fun x => fieldAdjacentTail_stationary a b L hb hs (t, x))
  have hsquare : gaussianTiltAverage (a + t) ζ
      (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) =
      fieldScalarSquares ((ζ, Real.toNNReal (a + t)) ::
        (η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh 1 := by
    have hm : Measurable (fun x => (G.X (t, x)) ^ 2) :=
      (G.mX.comp (by fun_prop)).pow_const 2
    have hmG : Measurable (fun x => G.U (t, x)) := G.mU.comp (by fun_prop)
    have htrans : gaussianTiltAverage (a + t) ζ
        (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) =
        fieldSpinTransition ζ (Real.toNNReal (a + t))
          (fun x => G.U (t, x)) (fun x => (G.X (t, x)) ^ 2) := by
      exact field_gaussianTiltAverage_eq_transition _ _ hmG hm
    rw [htrans]
    have hG : (fun x => G.U (t, x)) = fieldScalarValue
        ((η, Real.toNNReal (b - t)) :: S) (fun y => Real.log (Real.cosh y)) := by
      change gaussianTransform (b + -1 * t) η
        (fun x => F.U (t, x)) = _
      rw [neg_one_mul, ← sub_eq_add_neg, field_gaussianTransform_eq_operator]
      congr 1
      rw [show (fun x => F.U (t, x)) = (fun x => fieldAffineValue L (t, x)) from
        congrArg (fun f => fun x => f (t, x)) (fieldAffineFamily_value _ _ _ _),
        fieldAffineValue_scalar, fieldFixedAffine_increments]
      rfl
    rw [hG]
    have hGX : (fun x => G.X (t, x)) = fieldScalarMean
        ((η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh := adjacent_inner_mean a b η S hS t
    have hpow : (fun x => (G.X (t, x)) ^ 2) = fun x => (fieldScalarMean
        ((η, Real.toNNReal (b - t)) :: S)
        (fun y => Real.log (Real.cosh y)) Real.tanh x) ^ 2 := by
      funext x
      rw [congrFun hGX x]
    rw [hpow]
    rfl
  have hd := K.parameter_derivative t z ht
  have hfun : (fun q => K.U (q, z)) = fun q =>
      fieldScalarValue (fieldAdjacentIncrements P S a b ζ η q)
        (fun y => Real.log (Real.cosh y)) z := by
    funext q
    exact congrFun (hval q) z
  rw [hfun] at hd
  convert hd using 1
  rw [show K.T (t, z) = fieldScalarMean P (fun y => H.U (t, y))
      (fun y => H.T (t, y)) z from
      congrFun (fieldConstantPrefix_tangent isOpen_Ioo H P hP t) z,
    htan, fieldScalarMean_const_mul, hsquare, adjacent_value a b ζ η S hS t]
  simp only [fieldAdjacentLevel, fieldAdjacentIncrements]
  rw [fieldScalarSquares_append]

/-- The terminal height changes the final variance and the normalizing
subtraction by the same amount. -/
def fieldTerminalIncrements (P : List (ℝ × ℝ≥0)) (a ζ t : ℝ) :
    List (ℝ × ℝ≥0) := P ++ [(ζ, Real.toNNReal (a + t))]

def fieldTerminalLevel (P : List (ℝ × ℝ≥0)) (a ζ t : ℝ) :
    Fin ((fieldTerminalIncrements P a ζ t).length + 1) :=
  fieldAppendIndex P [(ζ, Real.toNNReal (a + t))] 1

theorem hasDerivAt_fieldTerminalValue
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < (av.2 : ℝ))
    (a ζ d t z : ℝ) (ht : t ∈ Ioi (-a)) :
    HasDerivAt (fun q => fieldScalarValue (fieldTerminalIncrements P a ζ q)
      (fun y => Real.log (Real.cosh y)) z - (d + q) / 2)
      (-(1 - ζ) / 2 * fieldScalarSquares (fieldTerminalIncrements P a ζ t)
        (fun y => Real.log (Real.cosh y)) Real.tanh (fieldTerminalLevel P a ζ t) z) t := by
  let H := fieldTerminalFamily a ζ
  let K := fieldConstantPrefix isOpen_Ioi H P hP
  let A : ℝ → ℝ := fun y => gaussianTiltAverage (a + t) ζ
    (fun x => Real.log (Real.cosh x)) (fun x => (Real.tanh x) ^ 2) y
  have hm : Measurable (fun x : ℝ => (Real.tanh x) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hA : Measurable A :=
    measurable_gaussianTiltAverage_param (measurable_logCosh.comp measurable_snd)
      (hm.comp measurable_snd) measurable_const measurable_id ζ
  have hAb : ∀ y, |A y| ≤ 1 := by
    intro y
    apply field_gaussianTiltAverage_bound _ _ measurable_logCosh logCosh_linearGrowth hm
    intro x
    rw [abs_pow]
    nlinarith [field_abs_tanh_le_one x, abs_nonneg (Real.tanh x)]
  have hval (q : ℝ) : (fun y => K.U (q, y)) =
      fieldScalarValue (fieldTerminalIncrements P a ζ q)
        (fun y => Real.log (Real.cosh y)) := by
    rw [show (fun y => K.U (q, y)) =
      fieldScalarValue P (fun y => H.U (q, y)) from
        fieldConstantPrefix_value isOpen_Ioi H P hP q,
      fieldTerminalFamily_value_eq_operator]
    change fieldScalarValue P (fieldScalarValue [(ζ, Real.toNNReal (a + q))]
      (fun y => Real.log (Real.cosh y))) = _
    exact (fieldScalarValue_append P [(ζ, Real.toNNReal (a + q))]
      (fun y => Real.log (Real.cosh y))).symm
  have htangent : (fun y => H.T (t, y)) = fun y => 1 / 2 + (-(1 - ζ) / 2) * A y := by
    funext y
    rw [fieldTerminalFamily_tangent]
    dsimp only [A]
    ring
  have hsquare : A = fieldScalarSquares [(ζ, Real.toNNReal (a + t))]
      (fun y => Real.log (Real.cosh y)) Real.tanh 1 := by
    dsimp only [A]
    rw [field_gaussianTiltAverage_eq_transition _ _ measurable_logCosh hm]
    rfl
  have hd := (K.parameter_derivative t z ht).sub
    (((hasDerivAt_const t d).add (hasDerivAt_id t)).div_const 2)
  change HasDerivAt (fun q => K.U (q, z) - (d + q) / 2)
    (K.T (t, z) - (0 + 1) / 2) t at hd
  have hfun : (fun q => K.U (q, z) - (d + q) / 2) = fun q =>
      fieldScalarValue (fieldTerminalIncrements P a ζ q)
        (fun y => Real.log (Real.cosh y)) z - (d + q) / 2 := by
    funext q
    rw [congrFun (hval q) z]
  rw [hfun] at hd
  convert hd using 1
  rw [show K.T (t, z) = fieldScalarMean P (fun y => H.U (t, y))
      (fun y => H.T (t, y)) z from
      congrFun (fieldConstantPrefix_tangent isOpen_Ioi H P hP t) z,
    htangent, fieldConstantPrefix_test_affine isOpen_Ioi H P hP t hA hAb,
    hsquare, fieldTerminalFamily_value_eq_operator]
  simp only [fieldTerminalLevel, fieldTerminalIncrements]
  rw [fieldScalarSquares_append]
  change _ = (1 / 2 + -(1 - ζ) / 2 * _) - (0 + 1) / 2
  simp only [fieldScalarValue, List.foldr_cons, List.foldr_nil]
  ring

end InvariantIsing

end

end OAI
