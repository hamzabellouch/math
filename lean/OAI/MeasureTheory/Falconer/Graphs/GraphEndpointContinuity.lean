import OAI.MeasureTheory.Falconer.Angular.CircleAngularBins
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability
import OAI.MeasureTheory.Falconer.Angular.SmoothRotatedCone
import OAI.MeasureTheory.Falconer.Graphs.GraphSignPartition
import OAI.MeasureTheory.Falconer.Estimates.DistanceForm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem continuous_circle_of_direction {E : Type*} [TopologicalSpace E]
    (f : UnitCircle → E) (hf : Continuous (fun θ => f (sourceUnitDirection θ))) :
    Continuous f := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let q : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hq : Continuous q := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro ω
    exact ⟨⟨sourceAngle ω, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle ω⟩
  exact (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
    (hf.comp continuous_subtype_val)

theorem inheritedCircleSymbol_continuous {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (x : Plane) :
    Continuous (inheritedCircleSymbol S b k Q ρ m N lam sig J i h x) :=
  continuous_circle_of_direction _
    (inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x).continuous

theorem sourceConeCircle_continuous (axis : ℝ) : Continuous (sourceConeCircle axis) :=
  continuous_circle_of_direction _ (sourceConeCircle_rotated_contDiff axis).continuous

theorem circleGraphSignPlus_continuous : Continuous circleGraphSignPlus := by
  exact graphSignPlus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem circleGraphSignMinus_continuous : Continuous circleGraphSignMinus := by
  exact graphSignMinus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem sourcePlaneWave_continuous (x : Plane) :
    Continuous (fun p : ℝ × UnitCircle => sourcePlaneWave p.1 p.2 x) := by
  unfold sourcePlaneWave
  fun_prop

noncomputable def graphBinWeight (n j k : ℕ) (p : UnitCircle × UnitCircle) : ℝ :=
  circleAngularBin n j p.1 * circleAngularBin n k p.2

noncomputable def graphDistanceWeight (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  (graphBinWeight n j k p : ℂ) * sourceConeCircle axis p.1 * conj (sourceConeCircle axis p.2)

noncomputable def graphProductWeight (plus : Bool) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  ((graphBinWeight n j k p *
    (if plus then circleGraphSignPlus p else circleGraphSignMinus p)) : ℝ)

theorem graphBinWeight_continuous (n j k : ℕ) : Continuous (graphBinWeight n j k) :=
  ((circleAngularBin_continuous n j).comp continuous_fst).mul
    ((circleAngularBin_continuous n k).comp continuous_snd)

theorem graphDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphDistanceWeight axis n j k) := by
  exact ((Complex.continuous_ofReal.comp (graphBinWeight_continuous n j k)).mul
    ((sourceConeCircle_continuous axis).comp continuous_fst)).mul
      (Complex.continuous_conj.comp ((sourceConeCircle_continuous axis).comp continuous_snd))

theorem graphProductWeight_continuous (plus : Bool) (n j k : ℕ) :
    Continuous (graphProductWeight plus n j k) := by
  cases plus <;> exact Complex.continuous_ofReal.comp
    ((graphBinWeight_continuous n j k).mul (by first
      | exact circleGraphSignMinus_continuous
      | exact circleGraphSignPlus_continuous))

theorem graphProductWeight_partition (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    graphProductWeight true n j k p + graphProductWeight false n j k p =
      (graphBinWeight n j k p : ℂ) := by
  simp only [graphProductWeight, Bool.false_eq_true, ↓reduceIte, ← Complex.ofReal_add]
  rw [← mul_add, (circleGraphSignPartition p).2.2, mul_one]

end PlanarFalconer

end OAI
