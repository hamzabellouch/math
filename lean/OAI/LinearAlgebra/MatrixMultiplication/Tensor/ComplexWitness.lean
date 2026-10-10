import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCW75LabelHierarchy
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteMMRealization
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators
open Filter

namespace MatrixMultiplication.ComplexWitness

open MatrixMultiplication.Foundation

structure FiniteRectangularWitness where
  outer : ℕ
  inner : ℕ
  multiplicity : ℕ
  rank : ℕ
  outer_pos : 0 < outer
  inner_pos : 0 < inner
  multiplicity_pos : 0 < multiplicity
  rank_pos : 0 < rank
  order : ℕ
  degree : ℕ
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixCoefficients (K := ℂ) (Fin outer) (Fin inner) (Fin outer)))
    rank order degree

abbrev CurveCoordinate := CW75Primitive.Word
abbrev CurveLeaf := CW75LabelHierarchy.Scalar

def curveApproximation :
    Tensor.PolynomialApproximation CW75Primitive.tensor 27 31 92 :=
  CW75Primitive.approximation

theorem curve_leaf_count : Fintype.card CurveLeaf = 75 :=
  CW75LabelHierarchy.scalar_card

theorem curve_leaf_coefficient (s : CurveLeaf) :
    CW75Primitive.tensor (CW75LabelHierarchy.x s) (CW75LabelHierarchy.y s)
      (CW75LabelHierarchy.z s) = 1 :=
  CW75LabelHierarchy.coefficient_one s

theorem curve_support_exhausted (x y z : CurveCoordinate)
    (h : CW75Primitive.tensor x y z ≠ 0) :
    ∃ s : CurveLeaf,
      (CW75LabelHierarchy.x s, CW75LabelHierarchy.y s, CW75LabelHierarchy.z s) =
        (x, y, z) :=
  CW75LabelHierarchy.support_exhausted x y z h

def curveFiber (u : CurveCoordinate) : Finset (List Elementary.BoundaryTerm) :=
  CW75LabelHierarchy.retainedWords.filter fun w =>
    CW75Primitive.listedX w 0 = u 0 ∧
    CW75Primitive.listedX w 1 = u 1 ∧
    CW75Primitive.listedX w 2 = u 2

def curveFiberSize (u : CurveCoordinate) : ℕ := (curveFiber u).card

theorem mem_curveFiber (u : CurveCoordinate) (w : List Elementary.BoundaryTerm) :
    w ∈ curveFiber u ↔
      w ∈ CW75LabelHierarchy.retainedWords ∧ CW75Primitive.listedX w = u := by
  simp only [curveFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hw, h0, h1, h2⟩
    refine ⟨hw, ?_⟩
    funext i
    fin_cases i <;> assumption
  · rintro ⟨hw, h⟩
    exact ⟨hw, congrFun h 0, congrFun h 1, congrFun h 2⟩

def curveFiberEquiv (u : CurveCoordinate) :
    {s : CurveLeaf // CW75LabelHierarchy.x s = u} ≃ ↥(curveFiber u) where
  toFun s := ⟨s.val.val, (mem_curveFiber u s.val.val).2
    ⟨s.val.property, s.property⟩⟩
  invFun s := ⟨⟨s.val, ((mem_curveFiber u s.val).1 s.property).1⟩,
    ((mem_curveFiber u s.val).1 s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem curveFiberSize_eq_card (u : CurveCoordinate) :
    curveFiberSize u =
      Fintype.card {s : CurveLeaf // CW75LabelHierarchy.x s = u} := by
  rw [Fintype.card_congr (curveFiberEquiv u), Fintype.card_coe]
  rfl

theorem curveFiberSize_pos : ∀ u : CurveCoordinate, 0 < curveFiberSize u := by
  decide

theorem curve_fiber_histogram :
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 1).card = 8 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 2).card = 12 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 4).card = 6 ∧
    (Finset.univ.filter fun u : CurveCoordinate => curveFiberSize u = 19).card = 1 := by
  decide

theorem curve_fiber_values : ∀ u : CurveCoordinate,
    curveFiberSize u = 1 ∨ curveFiberSize u = 2 ∨
      curveFiberSize u = 4 ∨ curveFiberSize u = 19 := by
  decide

theorem sum_curveLeaves_by_X (f : CurveCoordinate → ℝ) :
    (∑ s : CurveLeaf, f (CW75LabelHierarchy.x s)) =
      ∑ u : CurveCoordinate, (curveFiberSize u : ℝ) * f u := by
  classical
  rw [← Fintype.sum_fiberwise' CW75LabelHierarchy.x f]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← curveFiberSize_eq_card]

theorem sum_curveFiberSizes (f : ℕ → ℝ) :
    (∑ u : CurveCoordinate, f (curveFiberSize u)) =
      8 * f 1 + 12 * f 2 + 6 * f 4 + f 19 := by
  classical
  rcases curve_fiber_histogram with ⟨h1, h2, h4, h19⟩
  have he (u : CurveCoordinate) : f (curveFiberSize u) =
      (if curveFiberSize u = 1 then f 1 else 0) +
      (if curveFiberSize u = 2 then f 2 else 0) +
      (if curveFiberSize u = 4 then f 4 else 0) +
      (if curveFiberSize u = 19 then f 19 else 0) := by
    rcases curve_fiber_values u with h | h | h | h <;> simp [h]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, h1, h2, h4, h19, Nat.cast_ofNat, Nat.cast_one, one_mul]

abbrev CurveLabel := CW75LabelHierarchy.Label

def curveLabels : (n : ℕ) → CurveLeaf → CurveLabel n
  | 0 => CW75LabelHierarchy.outer
  | 1 => CW75LabelHierarchy.bPositions
  | 2 => CW75LabelHierarchy.bChoices
  | 3 => CW75LabelHierarchy.cPositions
  | 4 => CW75LabelHierarchy.aChoices
  | _ + 5 => fun _ _ => false

def curveFirstSide : ℕ → CW75LabelHierarchy.Side
  | 3 | 4 => .y
  | _ => .x

def curveSecondSide : ℕ → CW75LabelHierarchy.Side
  | 1 | 3 | 4 => .z
  | _ => .y

def curveFirstReader : (n : ℕ) → LabelRecord CurveLabel n → CurveCoordinate → CurveLabel n
  | 0, _ => CW75LabelHierarchy.outerX
  | 1, _ => CW75LabelHierarchy.bPositionsX
  | 2, _ => CW75LabelHierarchy.bChoicesX
  | 3, _ => CW75LabelHierarchy.cPositionsY
  | 4, prior => CW75LabelHierarchy.aChoicesY prior.1.1.2 prior.2
  | _ + 5, _ => fun _ _ => false

def curveSecondReader : (n : ℕ) → LabelRecord CurveLabel n → CurveCoordinate → CurveLabel n
  | 0, _ => CW75LabelHierarchy.outerY
  | 1, prior => CW75LabelHierarchy.bPositionsZ prior.2
  | 2, prior => CW75LabelHierarchy.bChoicesY prior.2
  | 3, prior => CW75LabelHierarchy.cPositionsZ prior.1.1.2
  | 4, _ => CW75LabelHierarchy.aChoicesZ
  | _ + 5, _ => fun _ _ => false

theorem curveFirstReader_readable (n : ℕ) (hn : n < 5) (s : CurveLeaf) :
    curveFirstReader n (labelRecordOf curveLabels n s)
        (CW75LabelHierarchy.originalCoordinate (curveFirstSide n) s) =
      curveLabels n s := by
  interval_cases n
  · exact CW75LabelHierarchy.outerX_read s
  · exact CW75LabelHierarchy.bPositionsX_read s
  · exact CW75LabelHierarchy.bChoicesX_read s
  · exact CW75LabelHierarchy.cPositionsY_read s
  · exact CW75LabelHierarchy.aChoicesY_read s

theorem curveSecondReader_readable (n : ℕ) (hn : n < 5) (s : CurveLeaf) :
    curveSecondReader n (labelRecordOf curveLabels n s)
        (CW75LabelHierarchy.originalCoordinate (curveSecondSide n) s) =
      curveLabels n s := by
  interval_cases n
  · exact CW75LabelHierarchy.outerY_read s
  · exact CW75LabelHierarchy.bPositionsZ_read s
  · exact CW75LabelHierarchy.bChoicesY_read s
  · exact CW75LabelHierarchy.cPositionsZ_read s
  · exact CW75LabelHierarchy.aChoicesZ_read s

theorem curve_completeRecord_injective :
    Function.Injective (labelRecordOf curveLabels 5) := by
  intro a b h
  apply CW75LabelHierarchy.positionLabels_injective
  exact Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.1.1.2) h)
    (Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.2) h)
      (Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.2) h)
        (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.1.2) h)))

def encodeCurveX (u : CurveCoordinate) : LabelRecord CurveLabel 3 :=
  (((PUnit.unit, CW75LabelHierarchy.outerX u),
    CW75LabelHierarchy.bPositionsX u), CW75LabelHierarchy.bChoicesX u)

def decodeCurveX (r : LabelRecord CurveLabel 3) : CurveCoordinate := fun i =>
  if r.2 i then 1 else if r.1.2 i then 2 else 0

theorem decode_encodeCurveX (u : CurveCoordinate) :
    decodeCurveX (encodeCurveX u) = u := by
  funext i
  simp only [decodeCurveX, encodeCurveX, CW75LabelHierarchy.bPositionsX,
    CW75LabelHierarchy.bChoicesX]
  have hd : ∀ v : Fin 3,
      (if decide (v = 1) then (1 : Fin 3) else if decide (v ≠ 0) then 2 else 0) = v := by
    decide
  exact hd (u i)

theorem encodeCurveX_injective : Function.Injective encodeCurveX :=
  Function.LeftInverse.injective decode_encodeCurveX

theorem curve_incidentPrefix (s : CurveLeaf) :
    labelRecordOf curveLabels 3 s = encodeCurveX (CW75LabelHierarchy.x s) := rfl

theorem curve_incidentPrefix_eq_iff (s t : CurveLeaf) :
    labelRecordOf curveLabels 3 s = labelRecordOf curveLabels 3 t ↔
      CW75LabelHierarchy.x s = CW75LabelHierarchy.x t := by
  rw [curve_incidentPrefix, curve_incidentPrefix, encodeCurveX_injective.eq_iff]

theorem curve_incidentPrefix_entropy (p : FiniteLaw CurveLeaf) :
    finiteEntropy (p.map (labelRecordOf curveLabels 3)).mass =
      finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  classical
  have hmass : (p.map (labelRecordOf curveLabels 3)).mass =
      ((p.map CW75LabelHierarchy.x).map encodeCurveX).mass := by
    funext r
    by_cases hr : ∃ u, encodeCurveX u = r
    · obtain ⟨u, rfl⟩ := hr
      rw [FiniteLaw.map_mass_apply _ _ encodeCurveX_injective]
      simp only [FiniteLaw.map_mass, curve_incidentPrefix, encodeCurveX_injective.eq_iff]
    · have hn (u : CurveCoordinate) : encodeCurveX u ≠ r := fun h => hr ⟨u, h⟩
      simp [FiniteLaw.map_mass, curve_incidentPrefix, hn]
  rw [hmass]
  exact FiniteLaw.map_entropy_of_injective _ _ encodeCurveX_injective

def curveReaderPair (n : Fin 5) : ReaderPair :=
  match n.val with
  | 1 => .xz
  | 3 | 4 => .yz
  | _ => .xy

theorem curveReaderPair_incident_prefix (n : Fin 5) :
    (curveReaderPair n = .xy ∨ curveReaderPair n = .xz) ↔ n.val < 3 := by
  fin_cases n <;> decide

theorem curveIncidentRate_eq_entropy_X (p : FiniteLaw CurveLeaf) :
    ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .xz =
        finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  rw [ConditionalLabels.incident_rate_eq_prefix_entropy p curveLabels 5 3
    (by decide) curveReaderPair curveReaderPair_incident_prefix]
  exact curve_incidentPrefix_entropy p

theorem curveHiddenRate_eq_entropy_sub_X (p : FiniteLaw CurveLeaf) :
    ConditionalLabels.lawPairingRate p curveLabels 5 curveReaderPair .yz =
      finiteEntropy p.mass - finiteEntropy (p.map CW75LabelHierarchy.x).mass := by
  rw [ConditionalLabels.remaining_rate_eq_entropy_sub_prefix p curveLabels 5 3
    (by decide) curveReaderPair curveReaderPair_incident_prefix curve_completeRecord_injective,
    curve_incidentPrefix_entropy]

theorem exists_finite_score_gt
    (W : ℕ → FiniteMMRealization) {β L : ℝ}
    (hlimit : Tendsto (fun n => (W n).rates.score β) atTop (nhds L))
    (hgap : Real.log 3 < L) :
    ∃ n, Real.log 3 < (W n).rates.score β :=
  (hlimit.eventually_const_lt hgap).exists

theorem omega_lt_of_score_limit
    (W : ℕ → FiniteMMRealization) {β L : ℝ}
    (hlimit : Tendsto (fun n => (W n).rates.score β) atTop (nhds L))
    (hgap : Real.log 3 < L) : Arithmetic.omega < β := by
  obtain ⟨n, hn⟩ := exists_finite_score_gt W hlimit hgap
  exact (W n).omega_lt_of_score_gt hn

end MatrixMultiplication.ComplexWitness

end

end OAI
