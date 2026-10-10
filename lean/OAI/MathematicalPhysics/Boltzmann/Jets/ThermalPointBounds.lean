import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput

namespace OAI

/-! # Uniform bounds for the actual thermal core velocity parameters -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermalPoint_transverse (α γ s d t : ℝ) (color : Bool)
    (x : JetPrototype.Space) (w : FiveGainMap.V) :
    transverse (thermalPoint α γ s d t color x w) = d • transverse (WithLp.toLp 2 w) := by
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap,PlaneChart.transverse_join]

theorem thermalPoint_axial (α γ s d t : ℝ) (color : Bool)
    (x : JetPrototype.Space) (w : FiveGainMap.V) :
    axial (thermalPoint α γ s d t color x w) =
      JetCoreMap.axialMap (JetPrototype.sign color) α γ s d t x.2 (w 2) := by
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap,PlaneChart.axial_join]
  rfl

theorem thermalPoint_transverse_bound {d : ℝ} (hd : 0 ≤ d)
    (α γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    ‖transverse (thermalPoint α γ s d t color x w)‖ ≤ d := by
  rw [thermalPoint_transverse,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
  have ht := (LargeOutput.transverse_norm_le (WithLp.toLp 2 w)).trans hw
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hd

theorem thermalPoint_axial_bound {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d)
    (γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    |axial (thermalPoint α γ s d t color x w)| ≤ d+1+α := by
  rw [thermalPoint_axial,JetCoreMap.axialMap]
  have ha : |w 2| ≤ 1 := (SmallInputGeometry.abs_axial_le_norm (WithLp.toLp 2 w)).trans hw
  have hu := AxialTransport.velocity_abs_le (σ := JetPrototype.sign color)
    (γ := γ) (s := s) (t := t) (z := x.2-t*d*(w 2)) hα
  have hsign : |JetPrototype.sign color| = 1 := by cases color <;> norm_num [JetPrototype.sign]
  rw [hsign] at hu
  calc
    _ ≤ |d*(w 2)|+|AxialFlow.velocity (JetPrototype.sign color) α γ s t (x.2-t*d*(w 2))| :=
      abs_add_le _ _
    _ ≤ d+(1+α) := add_le_add (by rw [abs_mul,abs_of_nonneg hd]; nlinarith) hu
    _ = _ := by ring

theorem thermalPoint_norm_bound {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) (hdmax : d ≤ 1)
    (γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    ‖thermalPoint α γ s d t color x w‖ ≤ α+3 := by
  have ht := thermalPoint_transverse_bound hd α γ s t color x w hw
  have ha := thermalPoint_axial_bound hα hd γ s t color x w hw
  have he := norm_sq_split (thermalPoint α γ s d t color x w)
  have ht0 := norm_nonneg (transverse (thermalPoint α γ s d t color x w))
  have ha0 := abs_nonneg (axial (thermalPoint α γ s d t color x w))
  have hn0 := norm_nonneg (thermalPoint α γ s d t color x w)
  have hts : ‖transverse (thermalPoint α γ s d t color x w)‖^2 ≤ d^2 := by nlinarith
  have has : (axial (thermalPoint α γ s d t color x w))^2 ≤ (d+1+α)^2 := by
    nlinarith [sq_abs (axial (thermalPoint α γ s d t color x w))]
  nlinarith

end BoltzmannNonuniqueness.JetCoreDensity

end

end OAI
