import OAI.Analysis.LipschitzHilbert.Estimates.WitnessTransfer
import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Horizontal projection size of actual compact popularity witnesses. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

/-- A compact set confined between two parallel lines has area at most its
horizontal projection length times its vertical thickness. -/
theorem projection_measure_bound (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {s c B : ℝ} (hB : 0 ≤ B)
    (hstrip : ∀ z ∈ E, |z.2 - s * z.1 - c| ≤ B) :
    (volume.prod volume).real E ≤ 2 * B * volume.real (Prod.fst '' E) := by
  let e := slopeShear (-s)
  have hecont : Continuous e := by
    change Continuous (fun z : ℝ × ℝ => (z.1, z.2 + -s * z.1))
    fun_prop
  have hproj : IsCompact (Prod.fst '' E) := hE.image continuous_fst
  have hsubset : e '' E ⊆ (Prod.fst '' E) ×ˢ Icc (c - B) (c + B) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    have hh := abs_le.mp (hstrip z hz)
    change c - B ≤ z.2 + -s * z.1 ∧ z.2 + -s * z.1 ≤ c + B
    constructor <;> linarith
  have hfinite : (volume.prod volume) ((Prod.fst '' E) ×ˢ Icc (c - B) (c + B)) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hproj.measure_lt_top.ne (by simp [Real.volume_Icc])
  have hbound := measureReal_mono hsubset hfinite
  rw [measureReal_prod_prod, Real.volume_real_Icc_of_le (by linarith)] at hbound
  have hpres := (slopeShear_measurePreserving (-s)).measure_preimage_equiv (e '' E)
  have hpreimage : e ⁻¹' (e '' E) = E := Set.preimage_image_eq E e.injective
  change (volume.prod volume) (e ⁻¹' (e '' E)) = (volume.prod volume) (e '' E) at hpres
  rw [hpreimage] at hpres
  have hreal : (volume.prod volume).real E = (volume.prod volume).real (e '' E) :=
    congrArg ENNReal.toReal hpres
  rw [hreal]
  calc
    _ ≤ volume.real (Prod.fst '' E) * (c + B - (c - B)) := hbound
    _ = _ := by ring

namespace SlopeBox

/-- The compact witness occupies a substantial horizontal set solely from
its area and the box-width bound. No measurable selection of fibers is used. -/
theorem witness_projection_lower (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q : ℝ} (hA : 0 < A) (hbox : ∀ z ∈ E, T.radius z ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E) :
    q * T.length / (2 * A) ≤ volume.real (Prod.fst '' E) := by
  have hw := T.width_pos
  have hstrip : ∀ z ∈ E, |z.2 - T.slope * z.1 - (T.y - T.slope * T.x)| ≤ A * T.width := by
    intro z hz
    have htrans : |T.transverse z| ≤ A := by
      have hh := hbox z hz
      unfold radius at hh
      linarith [abs_nonneg (T.horizontal z)]
    have heq : z.2 - T.slope * z.1 - (T.y - T.slope * T.x) =
        T.width * T.transverse z := by
      unfold transverse
      field_simp [T.width_pos.ne']
      ring
    rw [heq, abs_mul, abs_of_pos T.width_pos]
    nlinarith
  have hproj := projection_measure_bound E hE (mul_nonneg hA.le hw.le) hstrip
  apply (div_le_iff₀ (mul_pos (by norm_num) hA)).2
  nlinarith

end SlopeBox
end LipschitzHilbert

end

end OAI
