import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareSlabConvex
import Mathlib.Analysis.Convex.Deriv

namespace OAI

/-! The actual finite conditional overlap is convex in prescribed mean spin.
The ordinary root Gaussian is included in this identification. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma scalarFieldIncrements_exponent_le_one (h : FieldStep) :
    ∀ av ∈ scalarFieldIncrements h, av.1 ≤ 1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  change h.cut i.succ.castSucc ≤ 1
  rw [← h.last]
  exact h.ordered_cut.monotone (Fin.le_last _)

lemma magneticScalarSlabBias_root (h : FieldStep) :
    magneticScalarSlabBias (scalarFieldIncrements h) 0 (h.height 0) = magneticBias h := by
  have he : Real.toNNReal (h.height 0) = NNReal.mk (h.height 0) (h.nonneg 0) := Real.toNNReal_of_nonneg (h.nonneg 0)
  have hm : magneticScalarSlabMean (scalarFieldIncrements h) 0 (h.height 0) = fieldBiasMean h := by
    funext z
    simp only [magneticScalarSlabMean, fieldBiasMean, he]
  funext s
  change Function.invFun (magneticScalarSlabMean (scalarFieldIncrements h) 0 (h.height 0)) s =
    Function.invFun (fieldBiasMean h) s
  rw [hm]

lemma magneticFieldLevel_eq_slab (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fun s => magneticFieldLevel h s i) =
      magneticScalarSlabContinuation (scalarFieldIncrements h)
        (magneticScalarSquareFourJet (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
          (Fin.cast (by rw [scalarFieldIncrements_length]) i)).toMagneticContinuationJet
        0 (h.height 0) := by
  funext s
  rw [magneticScalarSlabContinuation_eq_jet _ (scalarFieldIncrements_positive h)]
  have he : Real.toNNReal (h.height 0) = NNReal.mk (h.height 0) (h.nonneg 0) := Real.toNNReal_of_nonneg (h.nonneg 0)
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    magneticScalarSquareFourJet_value, magneticScalarSlabBias_root, he,
    magneticFieldLevel, magneticLevelAtBias]

theorem magneticFieldLevel_second_deriv_nonneg (h : FieldStep)
    (i : Fin (h.depth + 1)) {s : ℝ} (hs : |s| < 1) :
    0 ≤ deriv (deriv (fun u => magneticFieldLevel h u i)) s := by
  rw [magneticFieldLevel_eq_slab]
  exact magneticScalarSlabSquare_deriv2_nonneg (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) (scalarFieldIncrements_exponent_le_one h)
    _ (le_refl (0 : ℝ)) (by norm_num) (h.nonneg 0) hs

theorem magneticFieldLevel_convexOn_spin (h : FieldStep) (i : Fin (h.depth + 1)) :
    ConvexOn ℝ (Ioo (-1 : ℝ) 1) (fun s => magneticFieldLevel h s i) := by
  let L := scalarFieldIncrements h
  let hL := scalarFieldIncrements_positive h
  let A := (magneticScalarSquareFourJet L hL
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)).toMagneticContinuationJet
  have he := magneticFieldLevel_eq_slab h i
  have hfirst (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) :
      DifferentiableAt ℝ (fun u => magneticFieldLevel h u i) s := by
    rw [he]
    exact (magneticScalarSlabContinuation_hasDerivAt_spin L hL A
      (le_refl (0 : ℝ)) (abs_lt.mpr hs) (h.height 0)).differentiableAt
  have hsecond (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) :
      DifferentiableAt ℝ (deriv (fun u => magneticFieldLevel h u i)) s := by
    rw [he]
    have hd := magneticScalarSlabContinuationSlope_hasDerivAt L hL A
      (le_refl (0 : ℝ)) (abs_lt.mpr hs) (h.height 0)
    apply HasDerivAt.differentiableAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact (magneticScalarSlabContinuation_hasDerivAt_spin L hL A
      (le_refl (0 : ℝ)) (abs_lt.mpr ht) (h.height 0)).deriv
  apply convexOn_of_deriv2_nonneg (convex_Ioo (-1 : ℝ) 1)
    (fun s hs => (hfirst s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfirst s (interior_subset hs)).differentiableWithinAt)
    (fun s hs => (hsecond s (interior_subset hs)).differentiableWithinAt)
  intro s hs
  exact magneticFieldLevel_second_deriv_nonneg h i (abs_lt.mpr (show s ∈ Ioo (-1 : ℝ) 1 from interior_subset hs))

end InvariantIsing

end

end OAI
