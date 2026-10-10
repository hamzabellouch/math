import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarFourJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarSlabEndpoint
import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap

namespace OAI

/-! The actual finite-level square continuations satisfy every endpoint
hypothesis of the inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSquareFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) : MagneticContinuationFourJet :=
  (fieldScalarSquares_has_bounded_fourJet L hL i).choose

lemma magneticScalarSquareFourJet_value (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    (magneticScalarSquareFourJet L hL i).value =
      fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i :=
  (fieldScalarSquares_has_bounded_fourJet L hL i).choose_spec

lemma magneticScalarSquareFourJet_sandwich (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : ℝ) :
    ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤
        (magneticScalarSquareFourJet L hL i).value z ∧
      (magneticScalarSquareFourJet L hL i).value z ≤ 1 := by
  rw [magneticScalarSquareFourJet_value]
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hm := fieldScalarSquares_monotone L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one z (show (0 : Fin (L.length + 1)) ≤ i by exact Fin.zero_le i)
  dsimp only at hm
  rw [fieldScalarSquares_zero] at hm
  exact ⟨hm, (fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one i).2 z |>.2⟩

theorem magneticScalarSlabSquareWeighted_tendsto_endpoint {ι : Type*} {l : Filter ι}
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (j : Fin (L.length + 1))
    {ζ c : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : c = -1 ∨ c = 1)
    (v s : ι → ℝ) (hs : ∀ᶠ i in l, |s i| < 1) (hslim : Tendsto s l (𝓝 c)) :
    Tendsto (fun i => magneticScalarSlabWeighted L hL
      (magneticScalarSquareFourJet L hL j).toMagneticContinuationJet ζ (v i) (s i)) l (𝓝 0) :=
  magneticScalarSlabWeighted_tendsto_endpoint L hL hL1 _
    (magneticScalarSquareFourJet_sandwich L hL j) hζ hζ1 hc v s hs hslim

end InvariantIsing

end

end OAI
