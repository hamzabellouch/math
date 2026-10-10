import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarInverse

namespace OAI

/-! The literal inverse-coordinate PDE of a finite Gaussian slab, with
spatial derivatives and inverse regularity discharged. Time here denotes
applied variance; reversing it gives the manuscript's backward equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) : MagneticContinuationJet :=
  let P := magneticLogCoshMeanJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  P.transition P ζ (Real.toNNReal v)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x))) hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)

lemma magneticScalarInverseCurvature_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s =
      (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v s) := by
  rw [magneticScalarInverseCurvature_eq]
  simp only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two]

lemma magneticScalarSlabJet_curvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < (magneticScalarSlabJet L hL ζ v).first z := by
  have hp := magneticScalarSlab_curvature_pos L hL hζ v z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two] using hp

def magneticScalarInverseSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  J.second b / J.first b

def magneticScalarInverseSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  J.third b / (J.first b) ^ 2 - (J.second b) ^ 2 / (J.first b) ^ 3

lemma magneticScalarSlabBias_hasDerivAt_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (1 / (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v s)) s := by
  have hd := magneticScalarSlabBias_hasDerivAt_spin L hL hζ hs v
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two, one_div] using hd

lemma magneticScalarInverseCurvature_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarInverseCurvature L hL ζ v)
      (magneticScalarInverseSlope L hL ζ v s) s := by
  have he : magneticScalarInverseCurvature L hL ζ v =
      fun t => (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v t) :=
    funext (magneticScalarInverseCurvature_eq_jet L hL ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v)
    ((magneticScalarSlabJet L hL ζ v).dFirst _)

lemma magneticScalarInverseSlope_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarInverseSlope L hL ζ v)
      (magneticScalarInverseSecond L hL ζ v s) s := by
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hd := inverse_mean_pullback_quotient
    (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
    (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v) rfl rfl
    (J.dSecond b) (J.dFirst b)
  convert hd using 1
  · rfl
  · dsimp only [magneticScalarInverseSecond, J, b]
    ring

lemma magneticScalarInverse_second_deriv (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    deriv (deriv (magneticScalarInverseCurvature L hL ζ v)) s =
      magneticScalarInverseSecond L hL ζ v s := by
  apply HasDerivAt.deriv
  apply (magneticScalarInverseSlope_hasDerivAt L hL hζ hs v).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticScalarInverseCurvature_hasDerivAt_spin L hL hζ (abs_lt.mpr ht) v).deriv

/-- The actual inverse curvature solves the forward-variance version of
`mag:inverse-PDE` on every positive-variance slab. -/
theorem magneticScalarInverseCurvature_PDE (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    HasDerivAt (fun t => magneticScalarInverseCurvature L hL ζ t s)
      ((magneticScalarInverseCurvature L hL ζ v s) ^ 2 / 2 *
        deriv (deriv (magneticScalarInverseCurvature L hL ζ v)) s +
        ζ * (magneticScalarInverseCurvature L hL ζ v s) ^ 2) v := by
  rw [magneticScalarInverse_second_deriv L hL hζ hs v,
    magneticScalarInverseCurvature_eq_jet]
  exact magneticScalarInverseCurvature_variance_hasDerivAt L hL hζ hs hv

end InvariantIsing

end

end OAI
