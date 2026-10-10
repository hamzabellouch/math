import OAI.Probability.InvariantIsing.Fields.FieldCompensatedTangent
import OAI.Probability.InvariantIsing.Fields.FieldScalarChain

namespace OAI

/-! Identification of the affine family with the already constructed
finite scalar values and physical conditional means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldAffineIncrements (L : List FieldAffineStep) (t : ℝ) : List (ℝ × ℝ≥0) :=
  L.map fun av => (av.exponent, Real.toNNReal (av.base + av.slope * t))

theorem fieldAffineValue_scalar (L : List FieldAffineStep) (t : ℝ) :
    (fun z => fieldAffineValue L (t, z)) =
      fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    change gaussianTransform (av.base + av.slope * t) av.exponent
        (fun z => fieldAffineValue L (t, z)) = _
    rw [field_gaussianTransform_eq_operator, ih]
    rfl

theorem fieldAffineFamily_mean (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) (t : ℝ) :
    (fun z => (fieldAffineFamily I hI L hL).X (t, z)) =
      fieldScalarMean (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldAffineFamily I hI L htail
    have hU : (fun z => G.U (t, z)) =
        fieldScalarValue (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) := by
      rw [show G.U = fieldAffineValue L from fieldAffineFamily_value I hI L htail]
      exact fieldAffineValue_scalar L t
    have hX : (fun z => G.X (t, z)) =
        fieldScalarMean (fieldAffineIncrements L t) (fun z => Real.log (Real.cosh z)) Real.tanh :=
      ih htail
    change gaussianTiltAverage (av.base + av.slope * t) av.exponent
      (fun z => G.U (t, z)) (fun z => G.X (t, z)) = _
    have hmU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
    have hmX : Measurable (fun z => G.X (t, z)) := G.mX.comp (by fun_prop)
    rw [field_gaussianTiltAverage_eq_transition _ _
      hmU hmX, hU, hX]
    rfl

theorem fieldAffineFamily_stationary (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t)
    (hs : ∀ av ∈ L, av.slope = 0) (p : ℝ × ℝ) :
    (fieldAffineFamily I hI L hL).T p = 0 := by
  induction L generalizing p with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldAffineFamily I hI L htail
    have hT : (fun y => G.T (p.1, y)) = fun _ => 0 := by
      funext y
      exact ih htail (fun bv hb => hs bv (List.mem_cons_of_mem av hb)) (p.1, y)
    change G.tangent av.base av.slope av.exponent p = 0
    unfold FieldSmoothFamily.tangent
    rw [hs av List.mem_cons_self, hT]
    simp only [zero_mul, add_zero, zero_div]
    have hmU : Measurable (fun z => G.U (p.1, z)) := G.mU.comp (by fun_prop)
    exact field_gaussianTiltAverage_const _ _ hmU (G.growth p.1) 0 p.2

end InvariantIsing

end

end OAI
