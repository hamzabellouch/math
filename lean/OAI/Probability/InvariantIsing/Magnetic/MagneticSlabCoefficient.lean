import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabPDE
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabBoundary
import OAI.Probability.InvariantIsing.Magnetic.MagneticJetProduct
import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteFourth

namespace OAI

/-! Uniform bounded potential for the actual finite-slab inverse-curvature
comparison. The cap depends on exponents, not on the variance parameter. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_eq_cons (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ) (v : ℝ) :
    magneticScalarSlabJet L hL ζ v =
      magneticLogCoshMeanJet ((ζ, Real.toNNReal v) :: L)
        (by intro av hav; rcases List.mem_cons.mp hav with h | h
            · simpa only [h] using hζ
            · exact hL av h) := by
  apply MagneticContinuationJet.eq_of_value_eq
  rfl

def magneticSlabPotentialCap (L : List (ℝ × ℝ≥0)) (ζ : ℝ) : ℝ :=
  magneticFourthRatioCap ((ζ, 0) :: L) + (magneticThirdRatioCap ((ζ, 0) :: L)) ^ 2

lemma magneticScalarInverse_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (v s : ℝ) :
    |magneticScalarInverseCurvature L hL ζ v s * magneticScalarInverseSecond L hL ζ v s| ≤
      magneticSlabPotentialCap L ζ := by
  let K := (ζ, Real.toNNReal v) :: L
  have hK : ∀ av ∈ K, 0 < av.1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ
    · exact hL av h
  have hK1 : ∀ av ∈ K, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ1
    · exact hL1 av h
  let b := magneticScalarSlabBias L ζ v s
  let J := magneticScalarSlabJet L hL ζ v
  have hq : 0 < J.first b := magneticScalarSlabJet_curvature_pos L hL hζ.le v b
  have hr : |J.second b| ≤ magneticThirdRatioCap K * J.first b := by
    have hh := fieldScalarLogCoshThird_relative K hK b
    have he := magneticScalarSlabJet_eq_cons L hL hζ v
    change |J.second b| ≤ _
    dsimp only [J]
    rw [he]
    exact hh
  have hd : |J.third b| ≤ magneticFourthRatioCap K * J.first b := by
    have hh := fieldScalarLogCoshFourth_relative K hK hK1 b
    dsimp only [J]
    rw [magneticScalarSlabJet_eq_cons L hL hζ v]
    exact hh
  have hrq : |J.second b / J.first b| ≤ magneticThirdRatioCap K := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr hr
  have hdq : |J.third b / J.first b| ≤ magneticFourthRatioCap K := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr hd
  have he : magneticScalarInverseCurvature L hL ζ v s *
      magneticScalarInverseSecond L hL ζ v s =
      J.third b / J.first b - (J.second b / J.first b) ^ 2 := by
    rw [magneticScalarInverseCurvature_eq_jet]
    dsimp only [magneticScalarInverseSecond, J, b]
    field_simp [hq.ne']
  rw [he]
  have hr2 : |(J.second b / J.first b) ^ 2| ≤ (magneticThirdRatioCap K) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hrq 2
  have hh := (abs_sub _ _).trans (add_le_add hdq hr2)
  simpa only [magneticSlabPotentialCap, K, magneticFourthRatioCap, magneticThirdRatioCap] using hh

end InvariantIsing

end

end OAI
