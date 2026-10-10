import OAI.GroupTheory.PolycyclicRecognition.Algebra.FreeCoefficientCoinvariants

namespace OAI

/-! # Naturality of the bar-to-inhomogeneous coefficient comparison -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Finsupp.module

variable (G : Type) [Group G]

def barCoefficientChainFunctor : Rep.{0} ℤ G ⥤ ChainComplex (ModuleCat ℤ) ℕ where
  obj A := (Rep.barComplex ℤ G).coinvariantsTensorObj A
  map f := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℤ G).map f)
    (ComplexShape.down ℕ)).app (Rep.barComplex ℤ G)
  map_id A := by
    apply HomologicalComplex.Hom.ext
    funext n
    change ((Rep.coinvariantsTensor ℤ G).map (𝟙 A)).app _ = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

instance : (barCoefficientChainFunctor G).PreservesZeroMorphisms where
  map_zero A B := by
    ext n
    simp [barCoefficientChainFunctor]
    rfl

def barCoefficientInhomogeneousIso :
    barCoefficientChainFunctor G ≅ groupHomology.chainsFunctor ℤ G := by
  classical
  refine NatIso.ofComponents (fun A => (groupHomology.inhomogeneousChainsIso A).symm) ?_
  intro A B f
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add]
      erw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
    | tmul a u =>
      change Rep.coinvariantsTensorFreeToFinsupp B (Fin n → G)
          (Representation.Coinvariants.mk _ (f.hom a ⊗ₜ[ℤ] u)) =
        ((groupHomology.chainsMap (MonoidHom.id G) f).f n).hom
          (Rep.coinvariantsTensorFreeToFinsupp A (Fin n → G)
            (Representation.Coinvariants.mk _ (a ⊗ₜ[ℤ] u)))
      rw [groupHomology.chainsMap_id_f_hom_eq_mapRange]
      exact tensorFreeToFinsupp_natural (Fin n → G) A B f a u

def chainZeroOpcyclesHomologyIso :
    HomologicalComplex.opcyclesFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0 ≅
      homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0 :=
  NatIso.ofComponents (fun K => (ChainComplex.isoHomologyι₀ K).symm) (by
    intro K L f
    exact (ChainComplex.isoHomologyι₀_inv_naturality f).symm)

def inhomogeneousZeroHomologyIso :
    groupHomology.chainsFunctor ℤ G ⋙ homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0 ≅
      Rep.coinvariantsFunctor ℤ G :=
  NatIso.ofComponents (fun A => groupHomology.H0Iso A) (by
    intro A B f
    exact groupHomology.map_id_comp_H0Iso_hom f)

def barCoefficientOpcyclesIso :
    barCoefficientChainFunctor G ⋙
      HomologicalComplex.opcyclesFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0 ≅
      Rep.coinvariantsFunctor ℤ G :=
  Functor.isoWhiskerLeft (barCoefficientChainFunctor G) chainZeroOpcyclesHomologyIso ≪≫
    Functor.isoWhiskerRight (barCoefficientInhomogeneousIso G)
      (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0) ≪≫
    inhomogeneousZeroHomologyIso G

end PolycyclicRecognition

end

end OAI
