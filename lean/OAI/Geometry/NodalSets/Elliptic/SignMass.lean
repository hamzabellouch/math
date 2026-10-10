import OAI.Geometry.NodalSets.Elliptic.SignScalePacking

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma compact_sign_mass_pos {Q : Set Coord} (hQ : IsCompact Q) (hvol : volume Q ≠ 0)
    (s : Coord → ℝ) (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    0 < ∫ x in Q, s x := by
  have hm : 0 < volume.real Q := ENNReal.toReal_pos hvol hQ.measure_ne_top
  have hh := setIntegral_mono_on (μ := volume)
    (integrableOn_const hQ.measure_ne_top : IntegrableOn (fun _ : Coord ↦ (2:ℝ)) Q)
    (hs.integrableOn_compact hQ) hQ.measurableSet hlo
  rw [setIntegral_const,smul_eq_mul] at hh
  linarith

namespace LocalCompactWaveData
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
    {D : Set Coord} {m J K k0 : ℕ}

lemma source_sign_mass_pos (a : LocalCompactWaveData g w S D m J K k0)
    {Q : Set Coord} (hQ : IsCompact Q) (hvol : volume Q ≠ 0) (hQD : Q ⊆ D) :
    0 < ∫ x in Q, sourceSignScale g S x :=
  compact_sign_mass_pos hQ hvol _ (a.source_sign_scale_continuousOn hQD)
    (fun x hx ↦ a.source_sign_scale_lower x (hQD hx))

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
