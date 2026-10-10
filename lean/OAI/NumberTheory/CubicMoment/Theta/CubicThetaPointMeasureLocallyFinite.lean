import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicMeasure

namespace OAI

/-! Hyperbolic measure is finite on each compact positive-height set;
the singularity at height zero stays outside every such compact set. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPointCoordinates_continuous : Continuous cubicThetaPointCoordinates :=
  continuous_subtype_val

lemma cubicThetaPointMeasure_compact {K : Set CubicThetaPoint} (hK : IsCompact K) :
    cubicThetaPointMeasure K<⊤ := by
  let L := cubicThetaPointCoordinates '' K
  have hL : IsCompact L := hK.image cubicThetaPointCoordinates_continuous
  have hpos : ∀ p∈L,0<p.2 := by
    rintro p ⟨q,_,rfl⟩
    exact q.property
  have hc : ContinuousOn (fun p : ℂ × ℝ => (p.2^3)⁻¹) L := by
    intro p hp
    exact ((continuous_snd.continuousAt.pow 3).inv₀ (pow_ne_zero 3 (hpos p hp).ne')).continuousWithinAt
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hc
  rw [cubicThetaPointMeasure_apply hK.isClosed.measurableSet]
  change cubicThetaHyperbolicMeasure L<⊤
  unfold cubicThetaHyperbolicMeasure
  rw [withDensity_apply']
  calc
    _ ≤ ∫⁻ _ in L, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hL.isClosed.measurableSet] with p hp
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (hC p hp)
    _ = ENNReal.ofReal C*volume L := by simp only [lintegral_const,Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL.measure_lt_top

instance cubicThetaPointMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts cubicThetaPointMeasure :=
  ⟨fun _K hK => cubicThetaPointMeasure_compact hK⟩

end CubicFirstMoment

end

end OAI
