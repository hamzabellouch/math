import OAI.Algebra.AuslanderReiten.Triangular.TriangularFunctor
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

private instance finitePiProjective {S P ι : Type*} [Ring S] [AddCommGroup P]
    [Module S P] [Module.Projective S P] [Fintype ι] : Module.Projective S (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[S] (ι → P))

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

def eRegularInclusion : TriangularE k R F R →ₗ[Triangular R F] Triangular R F where
  toFun x := ⟨x.top, 0, BalancedTensor.runitLeft (S := R) x.bottom⟩
  map_add' x y := by ext <;> simp
  map_smul' a x := by
    ext
    · rfl
    · simp
    · change BalancedTensor.runitLeft (S := R)
          (BalancedTensor.tmul a.off x.top + a.bottom • x.bottom) =
        a.bottom • BalancedTensor.runitLeft (S := R) x.bottom + MulOpposite.op x.top • a.off
      rw [map_add, map_smul]
      exact add_comm _ _

def eRegularProjection : Triangular R F →ₗ[Triangular R F] TriangularE k R F R where
  toFun a := ⟨a.top, (BalancedTensor.runitLeft (k := k) (R := R) (S := R)).symm a.off⟩
  map_add' a b := by ext <;> simp
  map_smul' a b := by
    ext
    · rfl
    · change (BalancedTensor.runitLeft (S := R)).symm
          (a.bottom • b.off + MulOpposite.op b.top • a.off) =
        BalancedTensor.tmul a.off b.top +
          a.bottom • (BalancedTensor.runitLeft (S := R)).symm b.off
      apply (BalancedTensor.runitLeft (S := R)).injective
      rw [LinearEquiv.apply_symm_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
      exact add_comm _ _

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem eRegular_split :
    (eRegularProjection (k := k) (R := R) (F := F)).comp eRegularInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext
  · rfl
  · exact (BalancedTensor.runitLeft (S := R)).symm_apply_apply x.bottom

instance eRegular_projective : Module.Projective (Triangular R F) (TriangularE k R F R) :=
  Module.Projective.of_split eRegularInclusion eRegularProjection eRegular_split

def jRegularInclusion : TriangularJ k R F R →ₗ[Triangular R F] Triangular R F where
  toFun x := ⟨0, x.bottom, 0⟩
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

def jRegularProjection : Triangular R F →ₗ[Triangular R F] TriangularJ k R F R where
  toFun a := ⟨0, a.bottom⟩
  map_add' a b := by ext; simp
  map_smul' a b := by ext; simp

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] in
theorem jRegular_split :
    (jRegularProjection (k := k) (R := R) (F := F)).comp jRegularInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext
  exact rfl

instance jRegular_projective : Module.Projective (Triangular R F) (TriangularJ k R F R) :=
  Module.Projective.of_split jRegularInclusion jRegularProjection jRegular_split

variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]

omit [SMulCommClass k R M] in
theorem eProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (Triangular R F) (TriangularE k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective (Triangular R F) (TriangularE k R F (Fin n → R)) :=
    Module.Projective.of_equiv (ePi (k := k) (R := R) (F := F) (M := R) (Fin n)).symm
  apply Module.Projective.of_split (eMap s) (eMap p)
  rw [← eMap_comp, hs, eMap_id]

omit [SMulCommClass k R M] in
theorem jProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (Triangular R F) (TriangularJ k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective (Triangular R F) (TriangularJ k R F (Fin n → R)) :=
    Module.Projective.of_equiv (jPi (k := k) (R := R) (F := F) (M := R) (Fin n)).symm
  apply Module.Projective.of_split (jMap s) (jMap p)
  rw [← jMap_comp, hs, jMap_id]

end ArExplicit.TriangularInduction

end

end OAI
