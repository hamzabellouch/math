import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorForget
import OAI.Algebra.AuslanderReiten.Homology.VectorTensorKunneth

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem map_quasiIso {P P' : ChainComplex (ModuleCat.{u} A) ℕ}
    {Q Q' : ChainComplex (ModuleCat.{u} B) ℕ} (f : P ⟶ P') (g : Q ⟶ Q')
    [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)) := by
  let Φ := (forgetField k (A ⊗[k] B)).mapHomologicalComplex (ComplexShape.down ℕ)
  let f₀ := ((forgetField k A).mapHomologicalComplex (ComplexShape.down ℕ)).map f
  let g₀ := ((forgetField k B).mapHomologicalComplex (ComplexShape.down ℕ)).map g
  let t := mapBifunctorMap f₀ g₀ (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
    (ComplexShape.down ℕ)
  have : QuasiIso f₀ := inferInstance
  have : QuasiIso g₀ := inferInstance
  have : QuasiIso t := VectorComplex.totalMap_quasiIso k _ f₀ g₀
  have h := scalarForgetTotalIso_naturality k A B f g
  have : QuasiIso ((scalarForgetTotalIso k A B P Q).hom ≫
      Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) := by
    rw [← h]
    infer_instance
  have : QuasiIso (Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) :=
    (quasiIso_iff_comp_left (scalarForgetTotalIso k A B P Q).hom
      (Φ.map (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)))).mp inferInstance
  exact (quasiIso_map_iff_of_preservesHomology _ (forgetField k (A ⊗[k] B))).mp inferInstance

end ArExplicit.ExternalTensor

end

end OAI
