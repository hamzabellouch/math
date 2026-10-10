import Mathlib

namespace OAI

open CategoryTheory CategoryTheory.Limits Finsupp Representation Rep TensorProduct

universe u
namespace CanonicalShapiro
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def barLift (f : G →* H) (n : ℕ) :
    Rep.free k G (Fin n → G) ⟶ Rep.res f (Rep.free k H (Fin n → H)) :=
  Rep.freeLift k G _ (fun x => Finsupp.single (f ∘ x) (MonoidAlgebra.single 1 1))

@[simp] lemma barLift_single (f : G →* H) (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (barLift (k:=k) f n).hom (single x (MonoidAlgebra.single g r)) =
      single (f ∘ x) (MonoidAlgebra.single (f g) r) := by
  simp [barLift, Representation.freeLift_single_single]

lemma barLift_d (f : G →* H) (n : ℕ) :
    Rep.barComplex.d k G n ≫ barLift f n =
      barLift f (n+1) ≫ (Rep.resFunctor.{u,u,u,u} f).map (Rep.barComplex.d k H n) := by
  apply Rep.free_ext
  intro x
  change (barLift (k:=k) f n).hom
      ((Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single 1 1))) =
    (Rep.barComplex.d k H n).hom
      ((barLift (k:=k) f (n+1)).hom (single x (MonoidAlgebra.single 1 1)))
  rw [Rep.barComplex.d_single, barLift_single, map_one, Rep.barComplex.d_single]
  simp only [map_add, map_sum]
  congr 1
  · rw [barLift_single]
    rfl
  · apply Finset.sum_congr rfl
    intro j hj
    rw [barLift_single, map_one]
    congr 1
    simp [Fin.comp_contractNth]

noncomputable def barMap (f : G →* H) : Rep.barComplex k G ⟶
    ((Rep.resFunctor.{u,u,u,u} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex k H) where
  f n := barLift f n
  comm' i j h := by
    subst h
    simpa [ChainComplex.of.d] using
      (barLift_d (k:=k) f j).symm

lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial,
    Iso.trans_inv, Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single g 1 ⊗ₜ[k] MonoidAlgebra.single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      congr 1
      exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x)

@[simp] lemma bar_π_zero_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (MonoidAlgebra.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

lemma barMap_π (S : Subgroup G) :
    barMap (k:=k) S.subtype ≫
      ((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G)).π =
        (Rep.barResolution k S).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  apply Rep.free_ext
  intro x
  change (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution
    (Rep.barResolution k G)).π.f 0).hom
      ((barLift S.subtype 0).hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [barLift_single]
  change ((Rep.barResolution k G).π.f 0).hom
    (single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype 1) 1)) = _
  change ((Rep.barResolution k G).π.f 0).hom
    (single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype 1) 1)) =
      ((Rep.barResolution k S).π.f 0).hom (single x (MonoidAlgebra.single 1 1))
  rw [bar_π_zero_single, bar_π_zero_single]
noncomputable def barComparison (S : Subgroup G) :
    HomotopyEquiv (Rep.barComplex k S)
      (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G)).complex) :=
  (ProjectiveResolution.homotopyEquiv (Rep.barResolution k S)
    ((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G))).copy
    (ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial k S k)) _ (barMap S.subtype)
      (by
        change _ = (Rep.barResolution k S).π ≫
          (ChainComplex.single₀ (Rep k S)).map (𝟙 (Rep.trivial k S k))
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact ProjectiveResolution.homotopyEquiv_hom_π _ _)
      (by
        change _ = (Rep.barResolution k S).π ≫
          (ChainComplex.single₀ (Rep k S)).map (𝟙 (Rep.trivial k S k))
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact barMap_π (k:=k) S))

@[simp] lemma barComparison_hom (S : Subgroup G) :
    (barComparison (k:=k) S).hom = barMap S.subtype := rfl

noncomputable def indUnit (f : G →* H) (A : Rep.{u} k G) : A ⟶ Rep.res f (Rep.ind.{u,u,u,u} f A) :=
  Rep.indResHomEquiv f A (Rep.ind.{u,u,u,u} f A) (𝟙 _)

@[simp] lemma indUnit_apply (f : G →* H) (A : Rep.{u} k G) (a : A) :
    (indUnit f A).hom a = Representation.IndV.mk f A.ρ 1 a := by
  simp [indUnit, Rep.indResHomEquiv]

@[simp] lemma coinvariantsTensor_map_mk {A B C : Rep.{u} k G} (f : B ⟶ C) (a : A) (b : B) :
    (((Rep.coinvariantsTensor k G).obj A).map f) (Rep.coinvariantsTensorMk A B a b) =
      Rep.coinvariantsTensorMk A C a (f.hom b) := by
  simp [Rep.coinvariantsTensor, Rep.coinvariantsTensorMk]

noncomputable def tensorBarMap (S : Subgroup G) (A : Rep.{u} k S) :
    (Rep.barComplex k S).coinvariantsTensorObj A ⟶
      (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex).coinvariantsTensorObj A :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex _).map (barMap S.subtype)

lemma chainsIso_hom_single (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) :
    (groupHomology.inhomogeneousChainsIso A).hom.f n (single x a) =
      Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single 1 1)) := by
  change (Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)).symm (single x a) = _
  exact Rep.finsuppToCoinvariantsTensorFree_single x a

lemma chainsIso_inv_mk_single (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) :
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      (Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single 1 1))) = single x a := by
  rw [← chainsIso_hom_single]
  exact congrArg (fun f : groupHomology.inhomogeneousChains A ⟶
      groupHomology.inhomogeneousChains A => f.f n (single x a))
    (Iso.hom_inv_id (groupHomology.inhomogeneousChainsIso A))

lemma tensorBarMap_f_mk (S : Subgroup G) (A : Rep.{u} k S)
    (n : ℕ) (x : Fin n → S) (a : A) :
    (tensorBarMap S A).f n
      (Rep.coinvariantsTensorMk A (Rep.free k S (Fin n → S)) a
        (single x (MonoidAlgebra.single 1 1))) =
      Rep.coinvariantsTensorMk A (Rep.res S.subtype (Rep.free k G (Fin n → G))) a
        (single (S.subtype ∘ x) (MonoidAlgebra.single 1 1)) := by
  change (((Rep.coinvariantsTensor k S).obj A).map (barLift S.subtype n)) _ = _
  rw [coinvariantsTensor_map_mk, barLift_single, map_one]

noncomputable def resTensorIso (S : Subgroup G) (A : Rep.{u} k S) :
    ((((Rep.resFunctor.{u,u,u,u} S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex k G)).coinvariantsTensorObj A) ≅
      (Rep.barComplex k G).coinvariantsTensorObj (Rep.ind.{u,u,u,u} S.subtype A) :=
  groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)

lemma resTensorIso_hom_f (S : Subgroup G) (A : Rep.{u} k S) (n : ℕ) :
    (resTensorIso S A).hom.f n =
      Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G)) := rfl

lemma resIso_hom_f_mk (S : Subgroup G) (A : Rep.{u} k S)
    (n : ℕ) (b : Rep.free k G (Fin n → G)) (a : A) :
    (resTensorIso S A).hom.f n
      (Rep.coinvariantsTensorMk A (Rep.res S.subtype (Rep.free k G (Fin n → G))) a b) =
      Rep.coinvariantsTensorMk (Rep.ind.{u,u,u,u} S.subtype A) (Rep.free k G (Fin n → G))
        (Representation.IndV.mk S.subtype A.ρ 1 a) b := by
  rw [resTensorIso_hom_f]
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk S.subtype a b

lemma chainsMap_factorization (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    groupHomology.chainsMap S.subtype (indUnit S.subtype A) =
      (groupHomology.inhomogeneousChainsIso A).hom ≫ tensorBarMap S A ≫
      (resTensorIso S A).hom ≫
      (groupHomology.inhomogeneousChainsIso (Rep.ind.{u,u,u,u} S.subtype A)).inv := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  change (groupHomology.chainsMap S.subtype (indUnit S.subtype A)).f n (single x a) = _
  rw [groupHomology.chainsMap_f_single]
  change _ = (groupHomology.inhomogeneousChainsIso (Rep.ind.{u,u,u,u} S.subtype A)).inv.f n
    ((resTensorIso S A).hom.f n
      ((tensorBarMap S A).f n ((groupHomology.inhomogeneousChainsIso A).hom.f n (single x a))))
  rw [chainsIso_hom_single, tensorBarMap_f_mk, resIso_hom_f_mk, chainsIso_inv_mk_single,
    indUnit_apply]

noncomputable def chainsEquivalence (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    HomotopyEquiv (groupHomology.inhomogeneousChains A)
      (groupHomology.inhomogeneousChains (Rep.ind.{u,u,u,u} S.subtype A)) :=
  (HomotopyEquiv.ofIso (groupHomology.inhomogeneousChainsIso A)).trans
    ((((Rep.coinvariantsTensor k S).obj A).mapHomotopyEquiv (barComparison S)).trans
      ((HomotopyEquiv.ofIso (resTensorIso S A)).trans
        (HomotopyEquiv.ofIso (groupHomology.inhomogeneousChainsIso
          (Rep.ind.{u,u,u,u} S.subtype A)).symm)))

lemma chainsEquivalence_hom (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    (chainsEquivalence S A).hom =
      groupHomology.chainsMap S.subtype (indUnit S.subtype A) :=
  (chainsMap_factorization S A).symm

lemma isIso_map_indUnit (S : Subgroup G) (A : Rep.{u} k S) (n : ℕ) :
    IsIso (groupHomology.map S.subtype (indUnit S.subtype A) n) := by
  classical
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap S.subtype (indUnit S.subtype A)) n)
  rw [← chainsEquivalence_hom]
  exact (chainsEquivalence S A).toHomologyIso n |>.isIso_hom

end CanonicalShapiro

end OAI
