import OAI.Analysis.HyperbolicCones.MatrixLinear
import OAI.Analysis.HyperbolicCones.FormPositive

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem phi_outer_posSemidef (y : Fin 3 → ℝ) (v : Vec 4) :
    (phi y (outer v)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (phi_isHermitian y (outer v) (outerSym v).property)
  intro u
  have hr := phi_rank_one y (WithLp.toLp 2 u) v
  simpa only [star_trivial, hr] using choiLam_nonnegative
    (wedgeCoordinates v (WithLp.toLp 2 u)) y

theorem phi_posSemidef (y : Fin 3 → ℝ) (X : Mat 4 ℝ) (hX : X.PosSemidef) :
    (phi y X).PosSemidef := by
  obtain ⟨v, rfl⟩ := posSemidef_sum_outer X hX
  change ((phiLinear y) (∑ i, outer (v i))).PosSemidef
  rw [map_sum]
  exact Matrix.posSemidef_sum _ fun i _ => phi_outer_posSemidef y (v i)

theorem phi_monotone (y : Fin 3 → ℝ) : Monotone (phi y) := by
  intro X Z hXZ
  have hp := phi_posSemidef y (Z - X) hXZ
  change (phi y Z - phi y X).PosSemidef
  change ((phiLinear y) (Z - X)).PosSemidef at hp
  rw [map_sub] at hp
  exact hp

end Paper256

end

end OAI
