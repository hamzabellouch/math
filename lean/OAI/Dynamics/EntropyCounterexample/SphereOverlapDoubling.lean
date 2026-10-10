import OAI.Dynamics.EntropyCounterexample.SphereCoverGeometry
import OAI.Dynamics.EntropyCounterexample.CircleClockDoubling
import OAI.Dynamics.EntropyCounterexample.SphereDoublingCharts

namespace OAI

noncomputable section

namespace Problem340.SphereOverlapDoubling

open SphereCover

abbrev Overlap := ↥(northComplement ∩ southComplement)

def puncturedSquare (z : PuncturedPlane) : PuncturedPlane :=
  ⟨z.val ^ 2, pow_ne_zero 2 z.property⟩

lemma continuous_puncturedSquare : Continuous puncturedSquare :=
  (continuous_subtype_val.pow 2).subtype_mk _

lemma radialRetraction_square (z : PuncturedPlane) :
    radialRetraction (puncturedSquare z) = radialRetraction z ^ 2 := by
  apply Subtype.ext
  change ‖z.val ^ 2‖⁻¹ • z.val ^ 2 = (‖z.val‖⁻¹ • z.val) ^ 2
  rw [norm_pow, ← inv_pow, smul_pow]

def overlapSquare (x : Overlap) : Overlap :=
  overlapHomeomorph.symm (puncturedSquare (overlapHomeomorph x))

lemma continuous_overlapSquare : Continuous overlapSquare :=
  overlapHomeomorph.symm.continuous.comp
    (continuous_puncturedSquare.comp overlapHomeomorph.continuous)

lemma overlapSquare_coe (x : Overlap) :
    (overlapSquare x).val = SphereDoubling.sphereMap x.val := by
  change sphereOfComplex (sphereToComplex x.val ^ 2) = SphereDoubling.sphereMap x.val
  rw [← sphereDoubling_sphereOfComplex, sphereOfComplex_sphereToComplex x.property.1]

lemma overlapHomeomorph_square (x : Overlap) :
    overlapHomeomorph (overlapSquare x) = puncturedSquare (overlapHomeomorph x) :=
  overlapHomeomorph.apply_symm_apply _

lemma circleHomeomorphClock_eq : circleHomeomorphClock = circleClockHomeomorph := by
  ext z
  rfl

lemma overlapEquivClock_square (x : Overlap) :
    overlapEquivClock (overlapSquare x) =
      CircleClockDoubling.clockDouble (overlapEquivClock x) := by
  change circleHomeomorphClock (radialRetraction (overlapHomeomorph (overlapSquare x))) =
    CircleClockDoubling.clockDouble
      (circleHomeomorphClock (radialRetraction (overlapHomeomorph x)))
  rw [overlapHomeomorph_square, radialRetraction_square, circleHomeomorphClock_eq]
  change circleClockHomeomorph ((radialRetraction (overlapHomeomorph x) : Circle) ^ 2) =
    circleClockHomeomorph ((circleClockHomeomorph.symm
      (circleClockHomeomorph (radialRetraction (overlapHomeomorph x)))) ^ 2)
  exact congrArg circleClockHomeomorph
    (congrArg (fun z : Circle => z ^ 2)
      (circleClockHomeomorph.symm_apply_apply (radialRetraction (overlapHomeomorph x)))).symm

lemma overlapHomologyEquivClock_intertwines (n : ℕ)
    (v : RealSingularHomology n Overlap) :
    overlapHomologyEquivClock n
        (realHomologyMap n overlapSquare continuous_overlapSquare v) =
      realHomologyMap n CircleClockDoubling.clockDouble
        CircleClockDoubling.continuous_clockDouble (overlapHomologyEquivClock n v) := by
  change realHomologyMap n overlapEquivClock overlapEquivClock.continuous
      (realHomologyMap n overlapSquare continuous_overlapSquare v) =
    realHomologyMap n CircleClockDoubling.clockDouble
      CircleClockDoubling.continuous_clockDouble
      (realHomologyMap n overlapEquivClock overlapEquivClock.continuous v)
  have hcomp : (overlapEquivClock : Overlap → StandardClock) ∘ overlapSquare =
      CircleClockDoubling.clockDouble ∘ overlapEquivClock :=
    funext overlapEquivClock_square
  have hmap := congrArg (fun A => A v)
    (realHomologyMap_comp n overlapSquare overlapEquivClock continuous_overlapSquare
      overlapEquivClock.continuous).symm
  change realHomologyMap n overlapEquivClock overlapEquivClock.continuous
      (realHomologyMap n overlapSquare continuous_overlapSquare v) =
    realHomologyMap n (overlapEquivClock ∘ overlapSquare)
      (overlapEquivClock.continuous.comp continuous_overlapSquare) v at hmap
  have heq : realHomologyMap n (overlapEquivClock ∘ overlapSquare)
      (overlapEquivClock.continuous.comp continuous_overlapSquare) =
      realHomologyMap n (CircleClockDoubling.clockDouble ∘ overlapEquivClock)
        (CircleClockDoubling.continuous_clockDouble.comp overlapEquivClock.continuous) := by
    congr 1
  rw [hmap, heq, realHomologyMap_comp]
  rfl

end Problem340.SphereOverlapDoubling

end

end OAI
