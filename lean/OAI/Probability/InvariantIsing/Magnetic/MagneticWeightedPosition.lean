import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedNonnegative
import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareJet

namespace OAI

/-! Transport of the weighted continuation inequality back from the inverse
spin coordinate to every finite physical field position. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabMean_abs_lt_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |magneticScalarSlabMean L ζ v z| < 1 := by
  have hm := magneticScalarSlabMean_strictMono L hL hζ v
  have hb (x : ℝ) : |magneticScalarSlabMean L ζ v x| ≤ 1 :=
    magneticScalarSlabJet_value_bound L hL ζ v x
  have hlo := hm (show z - 1 < z by linarith)
  have hhi := hm (show z < z + 1 by linarith)
  have hminus := (abs_le.mp (hb (z - 1))).1
  have hplus := (abs_le.mp (hb (z + 1))).2
  exact abs_lt.mpr ⟨lt_of_le_of_lt hminus hlo, lt_of_lt_of_le hhi hplus⟩

lemma magneticScalarSlabBias_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    magneticScalarSlabBias L ζ v (magneticScalarSlabMean L ζ v z) = z := by
  apply (magneticScalarSlabMean_strictMono L hL hζ v).injective
  exact magneticScalarSlabMean_bias L hL hζ
    (magneticScalarSlabMean_abs_lt_one L hL hζ v z) v

lemma magneticScalarSlabWeighted_nonneg_at_position (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hi : ∀ z, 0 ≤ A.second z - A.first z *
      ((magneticLogCoshMeanJet L hL).second z / (magneticLogCoshMeanJet L hL).first z))
    {v : ℝ} (hv : 0 ≤ v) (z : ℝ) :
    let J := magneticScalarSlabJet L hL ζ v
    let K := magneticScalarSlabContinuationJet L hL A.toMagneticContinuationJet ζ v
    0 ≤ K.second z - K.first z * (J.second z / J.first z) := by
  have hinit : ∀ s, |s| < 1 →
      0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ 0 s := by
    intro s hs
    rw [magneticScalarSlabWeighted_zero]
    exact hi _
  have hn := magneticScalarSlabWeighted_nonneg L hL hL1 A hA hζ hζ1 hinit hv
    (magneticScalarSlabMean_abs_lt_one L hL hζ v z)
  simpa only [magneticScalarSlabWeighted, magneticScalarSlabBias_mean L hL hζ v z] using hn

end InvariantIsing

end

end OAI
