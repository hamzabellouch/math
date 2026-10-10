import OAI.Analysis.Nuclearity.UnitizedCompression
import OAI.Analysis.PureInfiniteness.CutSampleReturn

namespace OAI

/-! Norm identities that return the finite matrix estimates to the original
nonunital algebra and identify the two sampled moments. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma unitizationOneByOne_compression_norm (d a : A) :
    ‖(unitizationOneByOne d).conjTranspose * unitizationOneByOne a * unitizationOneByOne d -
      unitizationOneByOne a‖ = ‖star d * a * d - a‖ := by
  change ‖star (unitizationOneByOne d) * unitizationOneByOne a * unitizationOneByOne d -
    unitizationOneByOne a‖ = _
  rw [← map_star, ← map_mul, ← map_mul, ← map_sub]
  exact unitizationOneByOne_norm _

lemma unitizationOneByOne_commutator_norm (a b : A) :
    ‖unitizationOneByOne a * unitizationOneByOne b -
      unitizationOneByOne b * unitizationOneByOne a‖ = ‖a * b - b * a‖ := by
  rw [← map_mul, ← map_mul, ← map_sub]
  exact unitizationOneByOne_norm _

variable {D J : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Fintype J] [DecidableEq J]

lemma scalarSample_first_moment_norm (g : J → D) (t : J → ℝ)
    (hg : ∀ j, 0 ≤ g j) (a : D) :
    ‖columnReturn (sqrtColumn g) (scalarSample t) - CStarMatrix.toOneByOne (Fin 1) ℂ D a‖ =
      ‖(∑ j, (t j : ℂ) • g j) - a‖ := by
  rw [columnReturn_scalarSample t g hg]
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ D).toNonUnitalStarAlgHom
  change ‖e (∑ j, (t j : ℂ) • g j) - e a‖ = _
  rw [← map_sub]
  exact NonUnitalStarAlgHom.norm_map e (CStarMatrix.toOneByOne (Fin 1) ℂ D).injective _

lemma scalarSample_second_moment_norm (g : J → D) (t : J → ℝ)
    (hg : ∀ j, 0 ≤ g j) (a : D) :
    ‖columnReturn (sqrtColumn g) (scalarSample t * scalarSample t) -
      CStarMatrix.toOneByOne (Fin 1) ℂ D a * CStarMatrix.toOneByOne (Fin 1) ℂ D a‖ =
      ‖(∑ j, (((t j) ^ 2 : ℝ) : ℂ) • g j) - a * a‖ := by
  rw [scalarSample_square]
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ D).toNonUnitalStarAlgHom
  change ‖columnReturn (sqrtColumn g) (scalarSample (fun j => (t j) ^ 2)) - e a * e a‖ = _
  rw [← map_mul]
  exact scalarSample_first_moment_norm g (fun j => (t j) ^ 2) hg (a * a)

end WeakPureInfiniteness

end

end OAI
