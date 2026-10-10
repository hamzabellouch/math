import OAI.Analysis.KadisonKastler.PositiveCornerWitness
import OAI.Analysis.KadisonKastler.NormalizedCornerGeometry

namespace OAI

/-! # Normalization of the concrete two-sided corner coordinates -/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem modularQuadratic_isometry_inner (v : Algebra M) (hv : star v*v=1) (x y : H) :
    inner ℂ (modularQuadratic J v x) (modularQuadratic J v y)=inner ℂ x y :=
  (modularQuadratic J v).inner_map_map_iff_adjoint_comp_self.mpr
    ((modularQuadratic J v).isometry_iff_adjoint_comp_self.mp
      (modularQuadratic_isometry J hJ hright v hv)) x y

include hJ hright in
theorem modularCorner_pullback_norm (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x : H) :
    ‖modularQuadratic J (star v) x‖=‖modularQuadratic J q.val x‖ := by
  calc
    _ = ‖modularQuadratic J v (modularQuadratic J (star v) x)‖ :=
      ((modularQuadratic_isometry J hJ hright v hv).norm_map_of_map_zero (map_zero _) _).symm
    _ = _ := by
      change ‖(modularQuadratic J v*modularQuadratic J (star v)) x‖=_
      rw [modularQuadratic_mul J hJ hright,hq]

include hJ hright in
theorem modularCorner_push_normalize (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x : H) :
    modularQuadratic J v (normalize (modularQuadratic J (star v) x))=
      normalize (modularQuadratic J q.val x) := by
  change modularQuadratic J v (‖modularQuadratic J (star v) x‖⁻¹ •
    modularQuadratic J (star v) x)=‖modularQuadratic J q.val x‖⁻¹ • modularQuadratic J q.val x
  rw [ContinuousLinearMap.map_smul_of_tower,modularCorner_pullback_norm J hJ hright v hv q hq]
  congr 1
  change (modularQuadratic J v*modularQuadratic J (star v)) x=_
  rw [modularQuadratic_mul J hJ hright,hq]

include hJ hright in
theorem modularCorner_normalized_inner (v : Algebra M) (hv : star v*v=1)
    (q : AlgebraProjection M) (hq : v*star v=q.val) (x y : H) :
    inner ℂ (normalize (modularQuadratic J (star v) x))
        (normalize (modularQuadratic J (star v) y))=
      inner ℂ (normalize (modularQuadratic J q.val x)) (normalize (modularQuadratic J q.val y)) := by
  rw [← modularCorner_push_normalize J hJ hright v hv q hq x,
    ← modularCorner_push_normalize J hJ hright v hv q hq y,
    modularQuadratic_isometry_inner J hJ hright v hv]

end

end KadisonKastler

end OAI
