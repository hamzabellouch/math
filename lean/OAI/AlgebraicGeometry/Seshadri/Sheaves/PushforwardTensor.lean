import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPure

namespace OAI


                                           
section

namespace MaximalSeshadri.PushforwardTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def presheafHom (M N : X.Modules) :
    presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => pure M N (f ⁻¹ᵁ U.unop) m n)
    (fun m m' n => pure_add_left M N _ m m' n)
    (fun a m n => pure_smul_left M N _ ((f.app U.unop).hom a) m n)
    (fun m n n' => pure_add_right M N _ m n n')
    (fun a m n => pure_smul_right M N _ ((f.app U.unop).hom a) m n)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (pure_restrict M N ((Opens.map f.base).map i.unop) m n).symm

def hom (M N : X.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor X M N) :=
  ((adj Y).homEquiv _ _).symm (presheafHom f M N)

lemma hom_pure (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (hom f M N).app U
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n := by
  have h := ((adj Y).homEquiv
    (presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N))
    ((Scheme.Modules.pushforward f).obj (moduleTensor X M N))).apply_symm_apply (presheafHom f M N)
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(Y,U)] n)) h

@[reassoc] lemma naturality {M N P Q : X.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
      hom f P Q = hom f M N ≫ (Scheme.Modules.pushforward f).map (moduleTensorMap a b) := by
  apply TensorPure.hom_ext
  intro U m n
  change (hom f P Q).app U ((moduleTensorMap _ _).app U (pure _ _ U m n)) =
    (moduleTensorMap a b).app (f ⁻¹ᵁ U) ((hom f M N).app U (pure _ _ U m n))
  refine (congrArg ((hom f P Q).app U)
    (map_pure ((Scheme.Modules.pushforward f).map a)
      ((Scheme.Modules.pushforward f).map b) U m n)).trans ?_
  refine (hom_pure f P Q U _ _).trans ?_
  refine (map_pure a b (f ⁻¹ᵁ U) m n).symm.trans ?_
  exact congrArg ((moduleTensorMap a b).app (f ⁻¹ᵁ U)) (hom_pure f M N U m n).symm

end
end MaximalSeshadri.PushforwardTensor

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

lemma unit_hom (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleTensor Y M N) ≫
      (Scheme.Modules.pushforward f).map (hom f M N) =
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

@[reassoc] lemma naturality {M N P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫ hom f P Q =
      hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right]
  simp only [hom,Equiv.apply_symm_apply]
  rw [← Category.assoc,← moduleTensorMap_comp]
  rw [Category.assoc,← PushforwardTensor.naturality,← Category.assoc,← moduleTensorMap_comp]
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]

end
end MaximalSeshadri.PullbackTensor

end

end OAI
