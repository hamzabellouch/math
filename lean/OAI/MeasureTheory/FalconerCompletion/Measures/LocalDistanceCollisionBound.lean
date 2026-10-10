import Mathlib
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.ProjectionShiftedBandBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.FourPairLintegralRegroup

namespace OAI

/-! Measures and the conditional distance-set completion. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
open PlanarFalconer

theorem local_distance_collision_boundND (ρ : Measure V) [IsFiniteMeasure ρ]
    {P Q : Set V} (hP : MeasurableSet P) (hQ : MeasurableSet Q) (e : V) {w : ℝ} (hw : 0<w)
    (haff : ∀ x ∈ P, ∀ y ∈ Q, |dist x y-inner ℝ (x-y) e| ≤ w) {H : ℝ≥0∞}
    (hproj : ((ρ.restrict Q).prod (ρ.restrict Q)) {z : V × V | |inner ℝ (z.1-z.2) e| ≤ w} ≤ H) :
    (((ρ.restrict P).prod (ρ.restrict Q)).prod ((ρ.restrict P).prod (ρ.restrict Q)))
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
        (ρ P)^2*((bandOffsets 3).card*H) := by
  apply (pair_collision_fiber_boundND (ρ.restrict P) (ρ.restrict Q)
    _ (by measurability) (((bandOffsets 3).card : ℝ≥0∞)*H) ?_).trans_eq (by simp)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with xx hx hx'
  apply le_trans _ (mul_le_mul' le_rfl hproj)
  apply le_trans _ (projection_shifted_band_boundND (ρ.restrict Q) e hw 3 (inner ℝ (xx.1-xx.2) e))
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hQ),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hQ)] with yy hy hy'
  intro hc
  exact affine_distance_collisionND (haff xx.1 hx yy.1 hy) (haff xx.2 hx' yy.2 hy') hc

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V] in
lemma measure_smul_condND (ρ : Measure V) [IsFiniteMeasure ρ] (Q : Set V) :
    (ρ Q) • ProbabilityTheory.cond ρ Q=ρ.restrict Q := by
  by_cases hq : ρ Q=0
  · simp [hq,Measure.restrict_eq_zero.mpr hq]
  · rw [ProbabilityTheory.cond,smul_smul,ENNReal.mul_inv_cancel hq (measure_ne_top _ _),one_smul]

theorem local_distance_conditional_collisionND (ρ : Measure V) [IsFiniteMeasure ρ]
    {P Q : Set V} (hP : MeasurableSet P) (hQ : MeasurableSet Q) (e : V) {w : ℝ} (hw : 0<w)
    (haff : ∀ x ∈ P, ∀ y ∈ Q, |dist x y-inner ℝ (x-y) e| ≤ w) {B : ℝ≥0∞}
    (hproj : ((ProbabilityTheory.cond ρ Q).prod (ProbabilityTheory.cond ρ Q))
      {z : V × V | |inner ℝ (z.1-z.2) e| ≤ w} ≤ B) :
    (((ρ.restrict P).prod (ρ.restrict Q)).prod ((ρ.restrict P).prod (ρ.restrict Q)))
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
        ((bandOffsets 3).card:ℝ≥0∞)*B*(ρ P)^2*(ρ Q)^2 := by
  have hp : ((ρ.restrict Q).prod (ρ.restrict Q))
      {z : V × V | |inner ℝ (z.1-z.2) e| ≤ w} ≤ (ρ Q)^2*B := by
    rw [← measure_smul_condND ρ Q,Measure.prod_smul_left,Measure.prod_smul_right,
      smul_smul,Measure.smul_apply,smul_eq_mul]
    simpa only [pow_two] using mul_le_mul' (le_refl (ρ Q*ρ Q)) hproj
  exact (local_distance_collision_boundND ρ hP hQ e hw haff hp).trans_eq (by ring)

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
