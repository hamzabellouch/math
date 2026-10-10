import OAI.NumberTheory.TotientAsymptotic.PrefixConcentration

namespace OAI

/-! Discharging Ford's fixed-deviation coordinate input by elementary simplex caps. -/
noncomputable section
open MeasureTheory
namespace TotientAsymptotic

/-- The only distinction between the exact triangular simplex and Ford's
terminal inequality costs the fixed determinant factor `1/a₁`. -/
theorem fordCoordinateConcentrationInput : FordCoordinateConcentrationInput := by
  obtain ⟨C,c,hC,hc,hprefix⟩ := prefix_coordinate_concentration_unconditional
  have ha : 0 < a 1 := a_pos le_rfl
  refine ⟨C/a 1,c,0,div_pos hC ha,hc,?_⟩
  intro N _ B hB i hi
  have hfin := prefixRegion_volume_ne_top (by omega : 0 < N+2) B
  have hfordfin : volume (fordSimplex N B) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono (fun _ hu => hu.1))
  have hbadfin : volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hmono : (volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal ≤
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal :=
    ENNReal.toReal_mono hbadfin (measure_mono (fun _ hu => ⟨hu.1.1,hu.2⟩))
  have hvol := shrinkLast_volume_bound (prefixRegion (N+2) B 0 0) Set.univ
    MeasurableSet.univ (fun _ hu => hu) (fun _ _ => Set.mem_univ _)
  simp only [Set.inter_univ] at hvol
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfordfin) hvol
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr ha).le] at hreal
  calc
    _ ≤ (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal := hmono
    _ ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal :=
      hprefix N B hB i hi
    _ ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ))*((a 1)⁻¹*(volume (fordSimplex N B)).toReal) :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
