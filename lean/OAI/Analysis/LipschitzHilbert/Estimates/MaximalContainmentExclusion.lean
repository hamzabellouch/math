import OAI.Analysis.LipschitzHilbert.Geometry.DilatedRectangleInterior

namespace OAI

/-! The maximal selection rule excludes a later rectangle contained in
the interior half of an earlier dilation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {ι κ : Type*} [Fintype κ]

theorem interior_indicator_auxiliary_lower (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (S : Rectangle) (a : ℝ) (ha : 0 < a) {x : Plane}
    (hx : x ∈ (S.dilate (a/2) (half_pos ha)).carrier) :
    1 ≤ 36 * positiveAuxiliary e ((S.dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))) x := by
  let r := a*S.short/8
  have hr : 0 < r := div_pos (mul_pos ha S.short_pos) (by norm_num)
  let Q := centeredSquare (planeCoordinates.symm x) r
  let f := (S.dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))
  have hsub : Q ⊆ planeCoordinates ⁻¹' (S.dilate a ha).carrier := S.dilate_interior_square a ha hx
  have hQ : MeasurableSet Q := centeredSquare_measurable _ _
  have hint : (∫⁻ z in Q, f (planeCoordinates z) ∂volume.prod volume) = (volume.prod volume) Q := by
    calc
      _ = ∫⁻ _z in Q, (1:ℝ≥0∞) ∂volume.prod volume :=
        setLIntegral_congr_fun hQ (fun z hz => by
          have hz' : planeCoordinates z ∈ (S.dilate a ha).carrier := hsub hz
          exact indicator_of_mem hz' _)
      _ = _ := by simp
  have hc : planeCoordinates.symm x ∈ Q := by
    change (_ ∈ Icc _ _) ∧ (_ ∈ Icc _ _)
    constructor <;> constructor <;> linarith
  have haux := positiveAuxiliary_square_integral e f (planeCoordinates.symm x) r hr x hc
  rw [hint] at haux
  have hpos : (volume.prod volume) Q ≠ 0 := by
    rw [centeredSquare_volume]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have htop : (volume.prod volume) Q ≠ ∞ := by
    rw [centeredSquare_volume]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hpos htop).mp
  simpa only [mul_one,mul_assoc,mul_left_comm] using haux

theorem contained_in_earlier_dilation_blocked (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (hη : 36*η < 1)
    (previous : Finset ι) (s r : ι) (hs : s ∈ previous)
    (hsub : (R r).carrier ⊆ ((R s).dilate (a/2) (half_pos ha)).carrier) :
    maximalBlocked e R a ha η previous r := by
  let f := ((R s).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))
  have hf : f ≤ rectangleCount (fun j => (R j).dilate a ha) previous := by
    intro x
    exact Finset.single_le_sum
      (f := fun j => ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) x)
      (fun _ _ => zero_le) hs
  intro x hx
  have h := (interior_indicator_auxiliary_lower e (R s) a ha (hsub hx)).trans
    (mul_le_mul' le_rfl (positiveAuxiliary_mono e hf x))
  change η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) previous) x
  apply lt_of_not_ge
  intro hn
  exact (not_le_of_gt hη) (h.trans (mul_le_mul' le_rfl hn))

theorem unblocked_not_contained_in_earlier_dilation (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (hη : 36*η < 1)
    (previous : Finset ι) (s r : ι) (hs : s ∈ previous)
    (hnot : ¬maximalBlocked e R a ha η previous r) :
    ¬(R r).carrier ⊆ ((R s).dilate (a/2) (half_pos ha)).carrier := by
  intro hsub
  exact hnot (contained_in_earlier_dilation_blocked e R a ha η hη previous s r hs hsub)

end LipschitzHilbert

end

end OAI
