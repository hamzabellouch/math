import OAI.Probability.InvariantIsing.Fields.FieldTerminalOrder
import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap
import OAI.Probability.InvariantIsing.Fields.FieldSquarePrefix

namespace OAI

/-! The mixed-coordinate order after the final ordinary Gaussian root
average. Positive cascade exponents are required only for the interior
prefix; the root exponent remains zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarOverlaps_antitone_of_squares (P : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hP : ∀ av ∈ P, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hFG : HasLinearGrowth F)
    (hG : Measurable G) (hGG : HasLinearGrowth G)
    (ha : Measurable a) (haB : ∀ z, |a z| ≤ 1)
    (hb : Measurable b) (hbB : ∀ z, |b z| ≤ 1)
    (hle : ∀ i z, fieldScalarSquares P G b i z ≤ fieldScalarSquares P F a i z)
    (i : Fin (P.length + 1)) :
    fieldScalarOverlaps P root G b i ≤ fieldScalarOverlaps P root F a i := by
  have hrF := fieldScalarSquares_regular P hP hF hFG ha haB i
  have hrG := fieldScalarSquares_regular P hP hG hGG hb hbB i
  have hiF : Integrable (fieldScalarSquares P F a i) (gaussianReal 0 root) :=
    Integrable.of_bound hrF.1.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrF.2 z).1]
      exact (hrF.2 z).2)
  have hiG : Integrable (fieldScalarSquares P G b i) (gaussianReal 0 root) :=
    Integrable.of_bound hrG.1.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hrG.2 z).1]
      exact (hrG.2 z).2)
  exact integral_mono hiG hiF (hle i)

theorem fieldAdjacent_earlier_overlaps_antitone (a b ζ η : ℝ) (L : List FieldAffineStep)
    (hb : ∀ av ∈ L, 0 < av.base) (hs : ∀ av ∈ L, av.slope = 0)
    (hζ : 0 < ζ) (hζη : ζ ≤ η) (htail : ∀ av ∈ L, 0 < av.exponent)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1) (root : ℝ≥0)
    {t s : ℝ} (ht : t ∈ Ioo (-a) b) (hss : s ∈ Ioo (-a) b) (hts : t ≤ s)
    (i : Fin (P.length + 1)) :
    let G := fieldAdjacentFamily a b ζ η L hb hs
    fieldScalarOverlaps P root (fun y => G.U (s, y)) (fun y => G.X (s, y)) i ≤
      fieldScalarOverlaps P root (fun y => G.U (t, y)) (fun y => G.X (t, y)) i := by
  let G := fieldAdjacentFamily a b ζ η L hb hs
  have hshape q := fieldAdjacentFamily_shape a b ζ η L hb hs hζ
    (lt_of_lt_of_le hζ hζη) htail q
  exact fieldScalarOverlaps_antitone_of_squares P root hP
    (G.mU.comp (by fun_prop)) (G.growth t)
    (G.mU.comp (by fun_prop)) (G.growth s)
    (G.mX.comp (by fun_prop)) (fun z => (hshape t).2.2.2.2 z)
    (G.mX.comp (by fun_prop)) (fun z => (hshape s).2.2.2.2 z)
    (fieldAdjacent_earlier_squares_antitone a b ζ η L hb hs hζ hζη htail P hP ht hss hts) i

theorem fieldTerminal_earlier_overlaps_antitone (a ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1) (root : ℝ≥0)
    {t s : ℝ} (ht : t ∈ Ioi (-a)) (hs : s ∈ Ioi (-a)) (hts : t ≤ s)
    (i : Fin (P.length + 1)) :
    let G := fieldTerminalFamily a ζ
    fieldScalarOverlaps P root (fun y => G.U (s, y)) (fun y => G.X (s, y)) i ≤
      fieldScalarOverlaps P root (fun y => G.U (t, y)) (fun y => G.X (t, y)) i := by
  let G := fieldTerminalFamily a ζ
  have hshape q := fieldTerminalFamily_shape a ζ hζ0 q
  exact fieldScalarOverlaps_antitone_of_squares P root hP
    (G.mU.comp (by fun_prop)) (G.growth t)
    (G.mU.comp (by fun_prop)) (G.growth s)
    (G.mX.comp (by fun_prop)) (fun z => (hshape t).2.2.2.2 z)
    (G.mX.comp (by fun_prop)) (fun z => (hshape s).2.2.2.2 z)
    (fieldTerminal_earlier_squares_antitone a ζ hζ0 hζ1 P hP ht hs hts) i

end InvariantIsing

end

end OAI
