import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedPosition

namespace OAI

/-! Every finite conditional square mean is convex in the inverse mean
coordinate. This is derived by induction through the actual Gaussian steps. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSquareFourJet_zero_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    (magneticScalarSquareFourJet L hL 0).toMagneticContinuationJet =
      (magneticLogCoshMeanJet L hL).square := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  rw [magneticScalarSquareFourJet_value]
  exact fieldScalarSquares_zero L _ _ z

lemma magneticScalarSquareFourJet_succ_toJet (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ bv ∈ av :: L, 0 < bv.1) (i : Fin (L.length + 1)) :
    (magneticScalarSquareFourJet (av :: L) hL i.succ).toMagneticContinuationJet =
      magneticScalarSlabContinuationJet L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (magneticScalarSquareFourJet L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
          i).toMagneticContinuationJet av.1 (av.2 : ℝ) := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  rw [magneticScalarSquareFourJet_value]
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    Real.toNNReal_coe, magneticScalarSquareFourJet_value]
  rfl

lemma magneticSquareJet_weighted_nonneg (P : MagneticContinuationJet) (z : ℝ)
    (hq : P.first z ≠ 0) :
    0 ≤ P.square.second z - P.square.first z * (P.second z / P.first z) := by
  have he : P.square.second z - P.square.first z * (P.second z / P.first z) =
      2 * (P.first z) ^ 2 := by
    simp only [MagneticContinuationJet.square]
    field_simp [hq]
    ring
  rw [he]
  positivity

theorem magneticScalarSquare_inverse_convex (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) (z : ℝ) :
    let P := magneticLogCoshMeanJet L hL
    let A := magneticScalarSquareFourJet L hL i
    0 ≤ A.second z - A.first z * (P.second z / P.first z) := by
  induction L generalizing z with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hh : i.val < 1 := by simpa only [List.length_nil, zero_add] using i.isLt
      omega
    subst i
    dsimp only
    rw [show (magneticScalarSquareFourJet [] hL 0).second =
      (magneticLogCoshMeanJet [] hL).square.second from
        congrArg MagneticContinuationJet.second (magneticScalarSquareFourJet_zero_toJet [] hL)]
    rw [show (magneticScalarSquareFourJet [] hL 0).first =
      (magneticLogCoshMeanJet [] hL).square.first from
        congrArg MagneticContinuationJet.first (magneticScalarSquareFourJet_zero_toJet [] hL)]
    exact magneticSquareJet_weighted_nonneg _ z (fieldScalarLogCoshSecond_pos [] hL z).ne'
  | cons av L ih =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let ht1 := fun bv hb => hL1 bv (List.mem_cons_of_mem av hb)
    refine Fin.cases ?_ (fun j => ?_) i
    · have he := magneticScalarSquareFourJet_zero_toJet (av :: L) hL
      dsimp only
      rw [congrArg MagneticContinuationJet.second he, congrArg MagneticContinuationJet.first he]
      exact magneticSquareJet_weighted_nonneg _ z (fieldScalarLogCoshSecond_pos _ hL z).ne'
    · have hn := magneticScalarSlabWeighted_nonneg_at_position L ht ht1
        (magneticScalarSquareFourJet L ht j) (magneticScalarSquareFourJet_sandwich L ht j)
        (hL av List.mem_cons_self).le (hL1 av List.mem_cons_self)
        (fun x => ih ht ht1 j x) (show 0 ≤ (av.2 : ℝ) from av.2.property) z
      have hJ := magneticScalarSlabJet_eq_cons L ht (hL av List.mem_cons_self) (av.2 : ℝ)
      have hA := magneticScalarSquareFourJet_succ_toJet av L hL j
      dsimp only at hn ⊢
      rw [← hA, hJ] at hn
      simpa only [Real.toNNReal_coe] using hn

end InvariantIsing

end

end OAI
