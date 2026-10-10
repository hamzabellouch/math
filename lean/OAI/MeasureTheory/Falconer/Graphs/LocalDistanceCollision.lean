import OAI.MeasureTheory.Falconer.Graphs.PairCollisionTonelli
import OAI.MeasureTheory.Falconer.Radial.ProjectionShiftedBand

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem local_distance_collision_bound (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (P Q : DyadicSquare) (e : Plane) {w : ℝ} (hw : 0 < w)
    (haff : ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, |dist x y-planeDot (x-y) e| ≤ w)
    {H : ℝ≥0∞}
    (hproj : ((ρ.restrict Q.carrier).prod (ρ.restrict Q.carrier))
      {z : Plane × Plane | |planeDot (z.1-z.2) e| ≤ w} ≤ H) :
    (((ρ.restrict P.carrier).prod (ρ.restrict Q.carrier)).prod
      ((ρ.restrict P.carrier).prod (ρ.restrict Q.carrier)))
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
      (ρ P.carrier)^2 * (((bandOffsets 3).card : ℝ≥0∞)*H) := by
  apply (pair_collision_fiber_bound (ρ.restrict P.carrier) (ρ.restrict Q.carrier)
    _ (by measurability) (((bandOffsets 3).card : ℝ≥0∞)*H) ?_).trans_eq (by simp)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem P.measurable)] with xx hx hx'
  apply le_trans _ (mul_le_mul' le_rfl hproj)
  apply le_trans _ (projection_shifted_band_bound (ρ.restrict Q.carrier) e hw 3
    (planeDot (xx.1-xx.2) e))
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with yy hy hy'
  intro hc
  exact affine_distance_collision (haff xx.1 hx yy.1 hy) (haff xx.2 hx' yy.2 hy') hc

end PlanarFalconer

end OAI
