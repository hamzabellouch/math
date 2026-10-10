import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledContinuation

namespace OAI

/-! Exact initial square data for the induction over Gaussian levels. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticSquareContinuation_zero_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL 0).toMagneticContinuationJet ζ (0, s) = s ^ 2 := by
  by_cases hsi : |s| < 1
  · simp only [closedMagneticContinuation, hsi, ite_true]
    rw [magneticScalarSlabContinuation_eq_jet L hL,
      magneticScalarSlabContinuationJet_zero, magneticScalarSquareFourJet_value,
      fieldScalarSquares_zero]
    have hm := magneticScalarSlabMean_bias L hL hζ hsi (0 : ℝ)
    rw [magneticScalarSlabMean_zero] at hm
    rw [hm]
  · have he : |s| = 1 := le_antisymm (abs_le.mpr hs) (le_of_not_gt hsi)
    have hsq : s ^ 2 = 1 := by rw [← sq_abs, he]; norm_num
    simp only [closedMagneticContinuation, hsi, ite_false, hsq]

lemma closedMagneticSquareContinuation_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1)
    (i : Fin (L.length + 1)) (ζ s : ℝ) :
    closedMagneticContinuation (av :: L)
      (magneticScalarSquareFourJet (av :: L) hL i.succ).toMagneticContinuationJet ζ (0, s) =
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb)) i).toMagneticContinuationJet
      av.1 ((av.2 : ℝ), s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticContinuation, hs, ite_true]
    rw [magneticScalarSlabContinuation_eq_jet (av :: L) hL,
      magneticScalarSlabContinuationJet_zero, magneticScalarSlabBias_cons_initial,
      magneticScalarSlabContinuation_eq_jet L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb))]
    simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
      magneticScalarSquareFourJet_value, Real.toNNReal_coe]
    rfl
  · simp only [closedMagneticContinuation, hs, ite_false]

lemma magneticScaledSquareContinuation_zero_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) {ζ s : ℝ} (hζ : 0 ≤ ζ)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α 0 ζ (0, s) = s ^ 2 := by
  simpa only [magneticScaledSquareContinuation, magneticScaledSquareJet, mul_zero,
    Fin.cast_zero] using
    closedMagneticSquareContinuation_zero_initial (fieldScaleIncrements α L)
      (fieldScaleIncrements_positive α L hL) hζ hs

lemma magneticScaledSquareContinuation_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1)
    (α : ℝ≥0) (i : Fin (L.length + 1)) (ζ s : ℝ) :
    magneticScaledSquareContinuation (av :: L) hL α i.succ ζ (0, s) =
      magneticScaledSquareContinuation L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        α i av.1 ((av.2 : ℝ), s) := by
  have hi : (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) i.succ :
      Fin ((fieldScaleIncrements α (av :: L)).length + 1)) =
      (Fin.cast (by rw [fieldScaleIncrements_length]) i :
        Fin ((fieldScaleIncrements α L).length + 1)).succ := by
    apply Fin.ext
    rfl
  unfold magneticScaledSquareContinuation magneticScaledSquareJet
  rw [hi]
  convert closedMagneticSquareContinuation_cons_initial (av.1, α ^ 2 * av.2)
      (fieldScaleIncrements α L) (fieldScaleIncrements_positive α (av :: L) hL)
      (Fin.cast (by rw [fieldScaleIncrements_length]) i) ζ s using 1 <;>
    simp only [fieldScaleIncrements, List.map_cons, mul_zero, NNReal.coe_mul, NNReal.coe_pow]
  all_goals rfl

end InvariantIsing

end

end OAI
