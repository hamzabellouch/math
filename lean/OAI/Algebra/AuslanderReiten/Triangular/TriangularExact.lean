import OAI.Algebra.AuslanderReiten.Triangular.TriangularFunctor
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorExact

namespace OAI

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [SMulCommClass k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L] [SMulCommClass k R L]

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k R M] in
theorem eMap_exact [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (eMap (k := k) (F := F) e) (eMap d) := by
  have ht := BalancedTensor.mapRight_exact (k := k) (F := F) (S := R) e d hex
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex z.top).mp (congrArg TriangularModule.top hz)
    obtain ⟨y, hy⟩ := (ht z.bottom).mp (congrArg TriangularModule.bottom hz)
    exact ⟨⟨x, y⟩, TriangularModule.ext hx hy⟩
  · rintro ⟨w, rfl⟩
    apply TriangularModule.ext
    · exact (hex (e w.top)).mpr ⟨w.top, rfl⟩
    · exact (ht (BalancedTensor.mapRight (S := R) e w.bottom)).mpr ⟨w.bottom, rfl⟩

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] [Module k M] [IsScalarTower k R M] [SMulCommClass k R M]
  [Module k N] [IsScalarTower k R N] [SMulCommClass k R N]
  [Module k L] [IsScalarTower k R L] [SMulCommClass k R L] in
theorem jMap_exact (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (jMap (k := k) (F := F) e) (jMap d) := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex z.bottom).mp (congrArg TriangularModule.bottom hz)
    exact ⟨⟨0, x⟩, TriangularModule.ext (Subsingleton.elim _ _) hx⟩
  · rintro ⟨w, rfl⟩
    exact TriangularModule.ext (Subsingleton.elim _ _) ((hex (e w.bottom)).mpr ⟨w.bottom, rfl⟩)

end ArExplicit.TriangularInduction

end OAI
