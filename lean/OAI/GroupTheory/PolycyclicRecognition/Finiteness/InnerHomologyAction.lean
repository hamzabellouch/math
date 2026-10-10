import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerBarTranslation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyAction

namespace OAI

/-! # Inner conjugation is the identity on group homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G] (A : Rep ℤ G)

def innerHomologyCoefficient (a : G) : A ⟶ Rep.res (MulAut.conj a).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ a, by
    intro g
    change A.ρ a * A.ρ g = A.ρ (a * g * a⁻¹) * A.ρ a
    rw [← map_mul, ← map_mul]
    congr 1
    group⟩

theorem innerBarMap_tensor_chains [DecidableEq G] (a : G) :
    groupHomology.chainsMap (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) ≫
        (groupHomology.inhomogeneousChainsIso A).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map (innerBarMap a) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change Rep.finsuppToCoinvariantsTensorFree A (Fin i → G)
      ((groupHomology.chainsMap (MulAut.conj a).toMonoidHom
        (innerHomologyCoefficient A a)).f i (Finsupp.single x v)) =
    (((Rep.coinvariantsTensor ℤ G).obj A).map (innerBarFreeMap a i))
      (Rep.finsuppToCoinvariantsTensorFree A (Fin i → G) (Finsupp.single x v))
  rw [groupHomology.chainsMap_f_single, Rep.finsuppToCoinvariantsTensorFree_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Representation.Coinvariants.mk (A.ρ.tprod (Representation.free ℤ G (Fin i → G)))
      ((A.ρ a v) ⊗ₜ[ℤ] Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single 1 1)) =
    Representation.Coinvariants.mk (A.ρ.tprod (Representation.free ℤ G (Fin i → G)))
      (v ⊗ₜ[ℤ] (innerBarFreeMap a i).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [innerBarFreeMap_single, one_mul]
  have h := Representation.Coinvariants.mk_tmul_inv A.ρ
    (Representation.free ℤ G (Fin i → G)) v
    (Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single 1 1)) a
  rw [Representation.free_single_single, mul_one] at h
  exact h.symm

theorem innerHomologyMap_eq_id (a : G) (i : ℕ) :
    groupHomology.map (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) i =
      𝟙 (groupHomology A i) := by
  classical
  let F := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map (innerBarMap a)
  have hF : homologyMap F i = 𝟙 _ := by
    have h := (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopy
      (innerBarMapHomotopy a)).homologyMap_eq i
    let T := ((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)
    have hId : T.map (𝟙 (Rep.barComplex ℤ G)) = 𝟙 (T.obj (Rep.barComplex ℤ G)) :=
      T.map_id _
    change homologyMap F i = homologyMap (T.map (𝟙 (Rep.barComplex ℤ G))) i at h
    rw [hId, homologyMap_id] at h
    exact h
  have hc := congrArg (fun f => homologyMap f i) (innerBarMap_tensor_chains A a)
  rw [homologyMap_comp, homologyMap_comp] at hc
  change groupHomology.map (MulAut.conj a).toMonoidHom (innerHomologyCoefficient A a) i ≫
      homologyMap (groupHomology.inhomogeneousChainsIso A).hom i =
    homologyMap (groupHomology.inhomogeneousChainsIso A).hom i ≫ homologyMap F i at hc
  rw [hF, Category.comp_id] at hc
  exact (cancel_mono (homologyMap (groupHomology.inhomogeneousChainsIso A).hom i)).mp
    (hc.trans (Category.id_comp _).symm)

end PolycyclicRecognition

end

end OAI
