import OAI.Geometry.CylinderCovering.Simplex.OverlapVolume

namespace OAI

open Set MeasureTheory CylinderCovering

theorem CylinderCovering.tetrahedron_zero_shift_overlap_volume (v : Fin 4 → Euclidean 3) (hv : AffineIndependent ℝ v)
    {u : Euclidean 3} (hu : ‖u‖ = 1) :
    volume.real (simplexCarrier v ∩ (fun y => y - (0 : ℝ) • u) '' simplexCarrier v) =
      volume.real (simplexCarrier v) := by
  simpa only [zero_div, sub_zero, one_pow, one_mul] using
    tetrahedron_translated_overlap_volume v hv hu (le_refl (0 : ℝ))
    (simplex_longestChord_pos v hv hu)

end OAI
