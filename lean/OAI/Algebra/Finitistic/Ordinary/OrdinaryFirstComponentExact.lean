import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductProjective
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ProductModules
universe u
variable (L R : Type u) [Ring L] [Ring R]

instance firstFunctor_additive : (firstFunctor.{u,u} L R).Additive where
  map_add := by intros; rfl

/-- Exactness on the first central-idempotent component follows by projecting a preimage. -/
theorem firstFunctor_mapsExact (K : ShortComplex (ModuleCat.{u} (L × R))) (hK : K.Exact) :
    (K.map (firstFunctor L R)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
  intro y hy
  obtain ⟨x,hx⟩ := hK y.val (congrArg Subtype.val hy)
  refine ⟨⟨((1,0) : L × R) • x,?_⟩,?_⟩
  · change ((1,0) : L × R) • (((1,0) : L × R) • x) = ((1,0) : L × R) • x
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]
  · apply Subtype.ext
    change K.f.hom (((1,0) : L × R) • x) = y.val
    rw [K.f.hom.map_smul,hx,y.property]

instance firstFunctor_preservesHomology : (firstFunctor.{u,u} L R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (firstFunctor_mapsExact L R)

instance firstFunctor_preservesFiniteLimits : PreservesFiniteLimits (firstFunctor.{u,u} L R) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance firstFunctor_preservesFiniteColimits : PreservesFiniteColimits (firstFunctor.{u,u} L R) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Taking the first component of an inflated module recovers the original module. -/
def firstInflationComponentEquiv (M : ModuleCat.{u} L) :
    firstObject L R ((firstInflation L R).obj M) ≃ₗ[L] M where
  toFun x := x.val
  invFun x := ⟨x, one_smul L x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- This recovery is natural in every module and linear map. -/
def firstInflationComponentIso : firstInflation.{u,u} L R ⋙ firstFunctor L R ≅ 𝟭 (ModuleCat.{u} L) :=
  NatIso.ofComponents (fun M => (firstInflationComponentEquiv L R M).toModuleIso)
    (by intros; rfl)
end LittleFinitistic.ProductModules

end

end OAI
