import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledSlab
import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedInitial

namespace OAI

/-! Exact initial-data identification for induction over physical Gaussian
increments in the radial inverse-curvature comparison. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabBias_cons_initial (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (ζ s : ℝ) :
    magneticScalarSlabBias (av :: L) ζ 0 s = magneticScalarSlabBias L av.1 (av.2 : ℝ) s := by
  unfold magneticScalarSlabBias
  apply congrArg (fun f : ℝ → ℝ => Function.invFun f s)
  funext z
  rw [magneticScalarSlabMean_zero]
  simp only [fieldScalarMean, magneticScalarSlabMean, Real.toNNReal_coe]

lemma magneticScalarInverseCurvature_cons_initial (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ bv ∈ av :: L, 0 < bv.1) (ζ s : ℝ) :
    magneticScalarInverseCurvature (av :: L) hL ζ 0 s =
      magneticScalarInverseCurvature L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        av.1 (av.2 : ℝ) s := by
  have hp : 0 < av.1 := hL av List.mem_cons_self
  rw [magneticScalarInverseCurvature_eq_jet, magneticScalarSlabJet_zero,
    magneticScalarSlabBias_cons_initial, magneticScalarInverseCurvature_eq_jet,
    magneticScalarSlabJet_eq_cons L _ hp]
  simp only [Real.toNNReal_coe]

lemma magneticScaledClosedCurvature_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1)
    (α : ℝ≥0) (ζ s : ℝ) :
    magneticScaledClosedCurvature (av :: L) hL α ζ (0, s) =
      magneticScaledClosedCurvature L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        α av.1 ((av.2 : ℝ), s) := by
  by_cases hs : |s| < 1
  · simp only [magneticScaledClosedCurvature, mul_zero, fieldScaleIncrements, List.map_cons,
      closedMagneticScalarCurvature, hs, ite_true]
    rw [magneticScalarInverseCurvature_cons_initial]
    rfl
  · simp only [magneticScaledClosedCurvature, closedMagneticScalarCurvature, hs, ite_false, mul_zero]

end InvariantIsing

end

end OAI
