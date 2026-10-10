import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTangentSobolev

namespace OAI

/-! Identify the Borel measure used by the Sobolev library with the
canonical tangent volume. This removes the measurable-space diamond
without changing or postulating a measure. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment.LocalSobolev

private lemma canonicalVolume_transport (m : MeasurableSpace CubicThetaTangent)
    (hm : borel CubicThetaTangent=m) :
    letI : MeasurableSpace CubicThetaTangent := m
    letI : BorelSpace CubicThetaTangent := ⟨hm.symm⟩
    (volume : Measure CubicThetaTangent)=Eq.ndrec (motive:=fun m => @Measure CubicThetaTangent m) tangentBorelVolume hm := by
  subst m
  rfl

private lemma map_transport (m : MeasurableSpace CubicThetaTangent)
    (hm : borel CubicThetaTangent=m) :
    @Measure.map CubicThetaTangent (ℂ × ℝ) m inferInstance cubicThetaTangentCoordinates
        (Eq.ndrec (motive:=fun m => @Measure CubicThetaTangent m) tangentBorelVolume hm)=
      @Measure.map CubicThetaTangent (ℂ × ℝ) (borel CubicThetaTangent) inferInstance
        cubicThetaTangentCoordinates tangentBorelVolume := by
  subst m
  rfl

lemma tangentBorelVolume_map :
    @Measure.map CubicThetaTangent (ℂ × ℝ) (borel CubicThetaTangent) inferInstance
      cubicThetaTangentCoordinates tangentBorelVolume=volume := by
  have he := canonicalVolume_transport (inferInstance : MeasurableSpace CubicThetaTangent) BorelSpace.measurable_eq.symm
  have hm := tangentCoordinates_measurePreserving.map_eq
  rw [he,map_transport] at hm
  exact hm

lemma tangentBorelVolume_measurePreserving :
    letI : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
    MeasurePreserving cubicThetaTangentCoordinates tangentBorelVolume
      (volume : Measure (ℂ × ℝ)) := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact ⟨cubicThetaTangentCoordinates.continuous.measurable,tangentBorelVolume_map⟩

lemma tangentBorelVolume_integral (f : ℂ × ℝ → ℝ) :
    (∫ u, f (cubicThetaTangentCoordinates u) ∂tangentBorelVolume)=∫ y, f y := by
  let : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
  let : BorelSpace CubicThetaTangent := ⟨rfl⟩
  exact tangentBorelVolume_measurePreserving.integral_comp
    cubicThetaTangentCoordinates.toHomeomorph.measurableEmbedding f

end CubicFirstMoment.LocalSobolev

end

end OAI
