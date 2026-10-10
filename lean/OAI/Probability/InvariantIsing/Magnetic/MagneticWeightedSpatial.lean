import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarWeightedPDE

namespace OAI

/-! Actual spatial derivatives and the uniformly bounded potential of the
weighted inverse-coordinate continuation equation. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabFourJet_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < (magneticScalarSlabFourJet L hL ζ v).first z := by
  have he := congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)
  rw [he]
  exact magneticScalarSlabJet_curvature_pos L hL hζ v z

lemma magneticScalarSlabBias_hasDerivAt_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (1 / (magneticScalarSlabFourJet L hL ζ v).first (magneticScalarSlabBias L ζ v s)) s := by
  have he := congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)
  rw [he]
  exact magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v

def magneticScalarWeightedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabFourJet L hL ζ v
  let K := magneticScalarSlabContinuationFourJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  magneticWeightedJetFirst J K b / J.first b

def magneticScalarWeightedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) : ℝ :=
  magneticWeightedInverseSecond (magneticScalarSlabFourJet L hL ζ v)
    (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v s)

lemma magneticScalarSlabWeighted_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v)
      (magneticScalarWeightedSlope L hL A ζ v s) s := by
  have he : magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v =
      fun u => magneticWeightedJetValue (magneticScalarSlabFourJet L hL ζ v)
        (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v u) :=
    funext (magneticScalarSlabWeighted_eq_jet L hL A ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_fourJet L hL hζ hs v)
    (magneticWeightedJetValue_hasDerivAt _ _ (magneticScalarSlabFourJet_pos L hL hζ v _).ne')

lemma magneticScalarWeightedSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarWeightedSlope L hL A ζ v)
      (magneticScalarWeightedSecond L hL A ζ v s) s := by
  exact magneticWeightedInverseFirst_hasDerivAt _ _
    (magneticScalarSlabFourJet_pos L hL hζ v _).ne'
    (magneticScalarSlabBias_hasDerivAt_fourJet L hL hζ hs v)

lemma magneticScalarSlabWeighted_second_deriv (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    deriv (deriv (magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v)) s =
      magneticScalarWeightedSecond L hL A ζ v s := by
  apply HasDerivAt.deriv
  apply (magneticScalarWeightedSlope_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticScalarSlabWeighted_hasDerivAt_spin L hL A hζ (abs_lt.mpr ht) v).deriv

def magneticScalarWeightedPotential (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  magneticScalarInverseCurvature L hL ζ v s * magneticScalarInverseSecond L hL ζ v s +
    2 * ζ * magneticScalarInverseCurvature L hL ζ v s

lemma magneticScalarWeightedPotential_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hs : |s| < 1) (v : ℝ) :
    |magneticScalarWeightedPotential L hL ζ v s| ≤ magneticSlabPotentialCap L ζ + 2 := by
  have ha := magneticScalarInverseCurvature_pos L hL hζ v s
  have ha1 : magneticScalarInverseCurvature L hL ζ v s ≤ 1 :=
    (magneticScalarInverseCurvature_le_spin_variance L hL hL1 hζ hζ1 hs v).trans
      (by linarith [sq_nonneg s])
  have hb : |magneticScalarInverseCurvature L hL ζ v s *
      magneticScalarInverseSecond L hL ζ v s| ≤ magneticSlabPotentialCap L ζ := by
    rcases eq_or_lt_of_le hζ with he | hp
    · subst ζ
      exact magneticScalarInverse_zero_weighted_second_bound L hL hL1 v s
    · exact magneticScalarInverse_weighted_second_bound L hL hL1 hp hζ1 v s
  have hc : |2 * ζ * magneticScalarInverseCurvature L hL ζ v s| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hζ1) ha.le]
  exact (abs_add_le _ _).trans (add_le_add hb hc)

lemma magneticScalarWeightedPotential_eq_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v s : ℝ) :
    let J := magneticScalarSlabFourJet L hL ζ v
    let b := magneticScalarSlabBias L ζ v s
    magneticScalarWeightedPotential L hL ζ v s =
      J.third b / J.first b - (J.second b) ^ 2 / (J.first b) ^ 2 + 2 * ζ * J.first b := by
  let b := magneticScalarSlabBias L ζ v s
  have hq := (magneticScalarSlabFourJet_pos L hL hζ v b).ne'
  have h1 := congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)
  have h2 := congrArg MagneticContinuationJet.second (magneticScalarSlabFourJet_toJet L hL ζ v)
  have h3 := congrArg MagneticContinuationJet.third (magneticScalarSlabFourJet_toJet L hL ζ v)
  simp only [magneticScalarWeightedPotential, magneticScalarInverseCurvature_eq_jet,
    magneticScalarInverseSecond, ← h1, ← h2, ← h3]
  field_simp [hq]

theorem magneticScalarSlabWeighted_PDE (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (hs : |s| < 1) :
    HasDerivAt (fun t => magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ t s)
      ((magneticScalarInverseCurvature L hL ζ v s) ^ 2 / 2 *
        magneticScalarWeightedSecond L hL A ζ v s + magneticScalarWeightedPotential L hL ζ v s *
          magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s) v := by
  have hd := magneticScalarSlabWeighted_hasDerivAt_time L hL A hζ hv hs
  rw [magneticScalarWeightedPotential_eq_fourJet L hL hζ]
  rw [magneticScalarInverseCurvature_eq_jet,
    ← congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)]
  exact hd

end InvariantIsing

end

end OAI
