import OAI.NumberTheory.TotientAsymptotic.TailBoxAggregation

namespace OAI

/-! The prefix-times-tail-box measure is the usual full-coordinate volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

def joinCoordinates (R T : ℕ) :
    ((Fin R → ℝ) × (Fin T → ℝ)) ≃ᵐ (Fin (R+T) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin R ⊕ Fin T => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (R+T) => ℝ) finSumFinEquiv)

lemma joinCoordinates_left {R T : ℕ} (u : (Fin R → ℝ) × (Fin T → ℝ)) (i : Fin R) :
    joinCoordinates R T u (Fin.castAdd T i) = u.1 i := by
  simp [joinCoordinates, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, finSumFinEquiv]
  rfl

lemma joinCoordinates_right {R T : ℕ} (u : (Fin R → ℝ) × (Fin T → ℝ)) (i : Fin T) :
    joinCoordinates R T u (Fin.natAdd R i) = u.2 i := by
  simp [joinCoordinates, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, finSumFinEquiv]
  rfl

lemma joinCoordinates_preserves_volume (R T : ℕ) :
    MeasurePreserving (joinCoordinates R T) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (R+T) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin R ⊕ Fin T => ℝ))

lemma volume_joinCoordinates_image {R T : ℕ}
    (S : Set ((Fin R → ℝ) × (Fin T → ℝ))) :
    volume (joinCoordinates R T '' S) = volume S := by
  have hh := (joinCoordinates_preserves_volume R T).measure_preimage_equiv
    (joinCoordinates R T '' S)
  rw [Set.preimage_image_eq S (joinCoordinates R T).injective] at hh
  exact hh.symm

/-- A full-dimensional enclosure bounds the aggregated weighted prefix
volumes without multiplying by the number of tail witnesses. -/
theorem tail_box_aggregation_enclosure {R T : ℕ} (K : Finset (Fin T → ℕ))
    (S : (Fin T → ℕ) → Set (Fin R → ℝ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (W : Set (Fin (R+T) → ℝ)) (C : ℝ)
    (hC : 0 ≤ C) (hU : ∀ b ∈ K, MeasurableSet (U b))
    (hfin : volume W ≠ ⊤)
    (hsub : ∀ b ∈ K, ∀ p ∈ primeBoxTuples b, S p ⊆ U b)
    (hmass : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C)
    (henclose : joinCoordinates R T '' tailBoxLift K U ⊆ W) :
    (∑ p ∈ gridPrimeTuples K, reciprocalShiftWeight p * volume.real (S p)) ≤
      C * volume.real W := by
  have hmeasure : volume (tailBoxLift K U) ≤ volume W := by
    rw [← volume_joinCoordinates_image]
    exact measure_mono henclose
  have hUfin (b) (hb : b ∈ K) : volume (U b) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    apply le_trans _ hmeasure
    have hh : U b ×ˢ unitGridCell b ⊆ tailBoxLift K U := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hz⟩⟩
    have hm : volume (U b ×ˢ unitGridCell b) ≤ volume (tailBoxLift K U) := measure_mono hh
    simpa only [Measure.volume_eq_prod, Measure.prod_prod, volume_unitGridCell, mul_one] using hm
  exact (tail_box_aggregation K S U C hU hUfin hsub hmass).trans
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin hmeasure) hC)

end TotientAsymptotic

end

end OAI
