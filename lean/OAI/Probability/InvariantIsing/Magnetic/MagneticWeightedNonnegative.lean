import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedClosed
import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedInitial
import OAI.Probability.InvariantIsing.Magnetic.MagneticParabolicComparison

namespace OAI

/-! The actual weighted inverse-coordinate continuation preserves
nonnegativity. The maximum principle uses its proved zero endpoint limits. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScalarSlabWeighted_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hi : ∀ s, |s| < 1 →
      0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ 0 s)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s := by
  let W := closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ
  let Wt := closedMagneticWeightedTime L hL A ζ
  let Wx := closedMagneticWeightedSlope L hL A ζ
  let Wxx := closedMagneticWeightedSecond L hL A ζ
  let a := fun p => (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2
  let c := closedMagneticWeightedPotential L hL ζ
  have hw : ContinuousOn W (Icc (0 : ℝ) v ×ˢ Icc (-1 : ℝ) 1) :=
    (continuousOn_closedMagneticSlabWeighted L hL hL1 A hA hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)
  have hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x) := by
    intro x hx
    by_cases h : |x| < 1
    · simpa only [W, closedMagneticSlabWeighted, h, ite_true] using hi x h
    · simp only [W, closedMagneticSlabWeighted, h, ite_false, le_refl]
  have hdt : ∀ t ∈ Ioc (0 : ℝ) v, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t := by
    intro t ht x hx
    exact (closedMagneticSlabWeighted_hasDerivAt_time L hL A hζ ht.1 x).hasDerivWithinAt
  have hdx : ∀ t ∈ Icc (0 : ℝ) v, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x := by
    intro t ht x hx
    exact closedMagneticSlabWeighted_hasDerivAt_spin L hL A hζ (abs_lt.mpr hx) t
  have hdxx : ∀ t ∈ Icc (0 : ℝ) v, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x := by
    intro t ht x hx
    exact closedMagneticWeightedSlope_hasDerivAt_spin L hL A hζ (abs_lt.mpr hx) t
  have hb : ∀ t ∈ Icc (0 : ℝ) v,
      a (t, -1) = 0 ∧ (0 : ℝ) = 0 ∧ a (t, 1) = 0 ∧ (0 : ℝ) = 0 := by
    intro t ht
    obtain ⟨hminus, hplus⟩ := closedMagneticScalarCurvature_endpoints L hL ζ t
    simp only [a, hminus, hplus, zero_pow (by norm_num : 2 ≠ 0), zero_div, and_self]
  have hpde : ∀ p ∈ Ioc (0 : ℝ) v ×ˢ Icc (-1 : ℝ) 1,
      a p * Wxx p + (0 : ℝ) * Wx p + c p * W p ≤ Wt p := by
    intro p hp
    simp only [a, Wxx, c, W, Wt, closedMagneticWeightedTime, zero_mul, add_zero, le_refl]
  have hn := parabolic_minimum_nonneg_bounded hv W Wt Wx Wxx a (fun _ => 0) c hw hinit
    hdt hdx hdxx (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp => closedMagneticWeightedPotential_bound L hL hL1 hζ hζ1 p) hb hpde
  simpa only [W, closedMagneticSlabWeighted, hs, ite_true] using
    hn (v, s) ⟨⟨hv, le_rfl⟩, abs_le.mp hs.le⟩

lemma magneticScalarSlabWeighted_eq_curvature_square (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (v s : ℝ) :
    magneticScalarSlabWeighted L hL A ζ v s =
      (magneticScalarInverseCurvature L hL ζ v s) ^ 2 *
        magneticScalarSlabContinuationSecond L hL A ζ v s := by
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hq : J.first b ≠ 0 := (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
  rw [magneticScalarInverseCurvature_eq_jet]
  change K.second b - K.first b * (J.second b / J.first b) =
    (J.first b) ^ 2 * (K.second b / (J.first b) ^ 2 - K.first b * J.second b / (J.first b) ^ 3)
  field_simp [hq]

end InvariantIsing

end

end OAI
