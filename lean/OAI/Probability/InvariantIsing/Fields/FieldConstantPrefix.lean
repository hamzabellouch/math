import OAI.Probability.InvariantIsing.Fields.FieldAffineScalarBridge

namespace OAI

/-! Propagation of a covariance derivative through the unchanged earlier
levels. The propagated tangent is the actual conditional expectation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldConstantPrefix {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I) :
    (L : List (ℝ × ℝ≥0)) → (∀ av ∈ L, 0 < (av.2 : ℝ)) → FieldSmoothFamily I
  | [], _ => F
  | av :: L, hL =>
      (fieldConstantPrefix hI F L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))).transform
        hI av.2 0 av.1 (fun _ _ => by simpa only [zero_mul, add_zero] using hL av List.mem_cons_self)

theorem fieldConstantPrefix_value {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldConstantPrefix hI F L hL).U (t, z)) =
      fieldScalarValue L (fun z => F.U (t, z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F L htail
    change gaussianTransform ((av.2 : ℝ) + 0 * t) av.1 (fun z => G.U (t, z)) = _
    rw [field_gaussianTransform_eq_operator]
    simp only [zero_mul, add_zero, Real.toNNReal_coe]
    rw [show (fun z => G.U (t, z)) = fieldScalarValue L (fun z => F.U (t, z)) from ih htail]
    rfl

theorem fieldConstantPrefix_tangent {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldConstantPrefix hI F L hL).T (t, z)) =
      fieldScalarMean L (fun z => F.U (t, z)) (fun z => F.T (t, z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F L htail
    have hU := fieldConstantPrefix_value hI F L htail t
    have hT := ih htail
    have hmU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
    have hmT : Measurable (fun z => G.T (t, z)) := G.mT.comp (by fun_prop)
    change (fun z => G.tangent av.2 0 av.1 (t, z)) = _
    simp only [FieldSmoothFamily.tangent, zero_mul, zero_div, add_zero]
    rw [field_gaussianTiltAverage_eq_transition _ _ hmU hmT]
    simp only [Real.toNNReal_coe]
    rw [hU, hT]
    rfl

theorem fieldConstantPrefix_mean {I : Set ℝ} (hI : IsOpen I) (F : FieldSmoothFamily I)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < (av.2 : ℝ)) (t : ℝ) :
    (fun z => (fieldConstantPrefix hI F L hL).X (t, z)) =
      fieldScalarMean L (fun z => F.U (t, z)) (fun z => F.X (t, z)) := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    let htail := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let G := fieldConstantPrefix hI F L htail
    have hU := fieldConstantPrefix_value hI F L htail t
    have hX := ih htail
    have hmU : Measurable (fun z => G.U (t, z)) := G.mU.comp (by fun_prop)
    have hmX : Measurable (fun z => G.X (t, z)) := G.mX.comp (by fun_prop)
    change gaussianTiltAverage ((av.2 : ℝ) + 0 * t) av.1
      (fun z => G.U (t, z)) (fun z => G.X (t, z)) = _
    simp only [zero_mul, add_zero]
    rw [field_gaussianTiltAverage_eq_transition _ _ hmU hmX]
    simp only [Real.toNNReal_coe]
    rw [hU, hX]
    rfl

end InvariantIsing

end

end OAI
