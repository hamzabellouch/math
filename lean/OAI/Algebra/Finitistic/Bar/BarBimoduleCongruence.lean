import OAI.Algebra.Finitistic.Bar.TotalBarDerived

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor TensorProduct
open scoped TensorProduct
namespace DerivedBar.BimoduleTensor
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable {X Y : Type u}
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [Module D Y] [Module Dᵐᵒᵖ Y]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k D Y] [IsScalarTower k Dᵐᵒᵖ Y]
variable (e : X ≃ₗ[D] Y) (he : ∀ d : Dᵐᵒᵖ, ∀ x, e (d • x) = d • e x)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

include he in
omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k Dᵐᵒᵖ Y] [IsScalarTower k D V] in
private theorem leftMap_relations : relations k D X V ≤
    ((quotient k D Y V).comp (AlgebraTensorModule.rTensor k V e.toLinearMap)).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x,d,v,rfl⟩
  change quotient k D Y V (AlgebraTensorModule.rTensor k V e.toLinearMap
    ((MulOpposite.op d • x) ⊗ₜ[k] v - x ⊗ₜ[k] (d • v))) = 0
  simp only [_root_.map_sub, AlgebraTensorModule.rTensor_tmul, LinearEquiv.coe_coe, he]
  rw [balanced, sub_self]

/-- The actual left-factor map on the bar's balanced quotient. -/
def leftMap : tensor k D X V →ₗ[D] tensor k D Y V :=
  (relations k D X V).liftQ
    ((quotient k D Y V).comp (AlgebraTensorModule.rTensor k V e.toLinearMap))
      (leftMap_relations k D e he V)

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ Y] [IsScalarTower k Dᵐᵒᵖ Y] [IsScalarTower k D V] in
@[simp] theorem leftMap_quotient (x : X) (v : V) :
    leftMap k D e he V (quotient k D X V (x ⊗ₜ[k] v)) =
      quotient k D Y V (e x ⊗ₜ[k] v) := rfl

include he in
omit [SMulCommClass D Dᵐᵒᵖ X] [SMulCommClass D Dᵐᵒᵖ Y] in
private theorem symm_right (d : Dᵐᵒᵖ) (y : Y) : e.symm (d • y) = d • e.symm y := by
  apply e.injective
  simp only [LinearEquiv.apply_symm_apply, he]

/-- A genuine bimodule equivalence induces an equivalence of the actual balanced tensors. -/
def congrLeft : tensor k D X V ≃ₗ[D] tensor k D Y V :=
  LinearEquiv.ofLinearMap (leftMap k D e he V)
    (leftMap k D e.symm (symm_right D e he) V)
    (by
      apply (relations k D Y V).linearMap_qext
      apply AlgebraTensorModule.ext
      intro y v
      change quotient k D Y V (e (e.symm y) ⊗ₜ[k] v) = quotient k D Y V (y ⊗ₜ[k] v)
      rw [e.apply_symm_apply])
    (by
      apply (relations k D X V).linearMap_qext
      apply AlgebraTensorModule.ext
      intro x v
      change quotient k D X V (e.symm (e x) ⊗ₜ[k] v) = quotient k D X V (x ⊗ₜ[k] v)
      rw [e.symm_apply_apply])

local instance (N : ModuleCat.{u} D) : Module k N := scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Naturality in every input module retains the exterior D-action. -/
def tensorFunctorCongr : tensorFunctor k D X ≅ tensorFunctor k D Y :=
  NatIso.ofComponents (fun N => (congrLeft k D e he N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply (relations k D X N).linearMap_qext
    apply AlgebraTensorModule.ext
    intro x n
    rfl)

/-- The same actual tensor equivalence descends to the genuine bar-derived functor. -/
def derivedTensorCongr : derivedTensor k D X ≅ derivedTensor k D Y :=
  (Localization.fullyFaithfulWhiskeringLeft (chainQ D) (chainQuasiIso D) (chainDerived D)).preimageIso
    (derivedTensorResolutionIso k D X ≪≫
      isoWhiskerLeft (barTotalFunctor k D)
        (isoWhiskerRight (NatIso.mapHomologicalComplex (tensorFunctorCongr k D e he) (.down ℕ)) (chainQ D)) ≪≫
      (derivedTensorResolutionIso k D Y).symm)

/-- All finite genuine iterations are compatible with the original bimodule equivalence. -/
def derivedIterateCongr : (r : ℕ) → derivedTensorIterate k D X r ≅ derivedTensorIterate k D Y r
  | 0 => Iso.refl _
  | r+1 => isoWhiskerRight (derivedIterateCongr r) (derivedTensor k D X) ≪≫
      isoWhiskerLeft (derivedTensorIterate k D Y r) (derivedTensorCongr k D e he)
end DerivedBar.BimoduleTensor

end

end OAI
