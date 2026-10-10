import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Split Lie actions pass to invariant quotients

The simultaneous-basis form of Lie's theorem requires induction on a
quotient by a common eigenline. We prove the splitting hypothesis for
that quotient using images of the original generalized eigenspaces.
-/

namespace PolycyclicRecognition

open Module

variable {𝕜 : Type*} [Field 𝕜]

variable {L V : Type*} [LieRing L] [LieAlgebra 𝕜 L]
  [AddCommGroup V] [Module 𝕜 V] [LieRingModule L V] [LieModule 𝕜 L V]

/-- A quotient of a split Lie action remains split. The image of each
generalized eigenspace lies in the corresponding quotient eigenspace. -/
theorem quotient_isTriangularizable [LieModule.IsTriangularizable 𝕜 L V]
    (N : LieSubmodule 𝕜 L V) : LieModule.IsTriangularizable 𝕜 L (V ⧸ N) := by
  refine ⟨fun x => ?_⟩
  let q : V →ₗ[𝕜] V ⧸ N := N.toSubmodule.mkQ
  have hq : q.range = ⊤ := LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective
  have hcomm : (LieModule.toEnd 𝕜 L (V ⧸ N) x).comp q =
      q.comp (LieModule.toEnd 𝕜 L V x) := by
    ext v
    rfl
  apply le_antisymm le_top
  calc
    (⊤ : Submodule 𝕜 (V ⧸ N)) = (⊤ : Submodule 𝕜 V).map q := by
      rw [Submodule.map_top, hq]
    _ = (⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L V x).maxGenEigenspace μ).map q := by
      rw [LieModule.IsTriangularizable.maxGenEigenspace_eq_top x]
    _ ≤ ⨆ μ : 𝕜, (LieModule.toEnd 𝕜 L (V ⧸ N) x).maxGenEigenspace μ := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ => Module.End.map_genEigenspace_le q hcomm μ ⊤

end PolycyclicRecognition

end OAI
