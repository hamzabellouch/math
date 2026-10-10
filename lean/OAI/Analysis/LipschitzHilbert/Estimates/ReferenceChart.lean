import OAI.Analysis.LipschitzHilbert.Estimates.WitnessInterval
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral

namespace OAI

/-! Area-preserving reference-line coordinates for a top. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.SlopeBox

def referenceChart (T : SlopeBox) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1, z.2 + (T.y + T.slope * (z.1 - T.x)))
  invFun z := (z.1, z.2 - (T.y + T.slope * (z.1 - T.x)))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1, z.2 + (T.y + T.slope * (z.1 - T.x))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1, z.2 - (T.y + T.slope * (z.1 - T.x))))
    fun_prop

theorem referenceChart_measurePreserving (T : SlopeBox) :
    MeasurePreserving T.referenceChart (volume.prod volume) (volume.prod volume) := by
  change MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + (T.y + T.slope * (z.1 - T.x)))) _ _
  exact (MeasurePreserving.id volume).skew_product (by fun_prop)
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (T.y + T.slope * (x - T.x)))

theorem referenceChart_image_measure (T : SlopeBox) (E : Set (ℝ × ℝ)) :
    (volume.prod volume) (T.referenceChart '' E) = (volume.prod volume) E := by
  have h := T.referenceChart_measurePreserving.measure_preimage_equiv (T.referenceChart '' E)
  rw [Set.preimage_image_eq E T.referenceChart.injective] at h
  exact h.symm

theorem referenceChart_inverse_transverse (T : SlopeBox) (z : ℝ × ℝ) :
    (T.referenceChart.symm z).2 = T.width * T.transverse z := by
  change z.2 - (T.y + T.slope * (z.1 - T.x)) = _
  unfold transverse
  field_simp [T.width_pos.ne']
  ring

/-- A horizontal line in reference coordinates is the actual line through
the physical evaluation point in the reference direction. -/
theorem referenceChart_linePoint (T : SlopeBox) (z : ℝ × ℝ) (x : ℝ) :
    T.referenceChart (x, (T.referenceChart.symm z).2) =
      LipschitzHilbert.linePoint T.slope z x := by
  ext
  · rfl
  · change (z.2 - (T.y + T.slope * (z.1 - T.x))) +
        (T.y + T.slope * (x - T.x)) = z.2 + T.slope * (x - z.1)
    ring

def referenceRectangle (T : SlopeBox) (K : ℝ) : Set (ℝ × ℝ) :=
  T.witnessInterval K ×ˢ Icc (-K * T.width) (K * T.width)

/-- Every significant point lies in the fixed reference rectangle. -/
theorem significant_mem_referenceRectangle (T : SlopeBox) {K : ℝ} {z : ℝ × ℝ}
    (hz : T.radius z ≤ K) : T.referenceChart.symm z ∈ T.referenceRectangle K := by
  refine ⟨?_, ?_⟩
  · change z.1 ∈ T.witnessInterval K
    exact T.mem_witnessInterval hz
  apply mem_Icc.mpr
  have hv : |T.transverse z| ≤ K := by
    unfold radius at hz
    linarith [abs_nonneg (T.horizontal z)]
  have habs : |(T.referenceChart.symm z).2| ≤ K * T.width := by
    rw [T.referenceChart_inverse_transverse, abs_mul, abs_of_pos T.width_pos]
    nlinarith [T.width_pos]
  simpa only [neg_mul] using abs_le.mp habs

end LipschitzHilbert.SlopeBox

end

end OAI
