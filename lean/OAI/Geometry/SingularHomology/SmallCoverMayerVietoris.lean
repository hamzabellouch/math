import OAI.Geometry.SingularHomology.SingularSupportNaturality
import OAI.Geometry.SingularHomology.SimplicialMayerVietoris

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340

theorem simplicialMayerVietoris_sequence_eq_unionShortComplex
    {K : SSet} (A B : K.Subcomplex) :
    SimplicialMayerVietoris.sequence A B = SingularCover.unionShortComplex A B := rfl

namespace SmallCoverMayerVietoris

open SingularSmallChains

variable {X : Type} [TopologicalSpace X]

def binaryCover (U V : Set X) : Bool → Set X := fun b => cond b U V

@[simp] theorem small_binaryCover (U V : Set X) :
    small (binaryCover U V) = inSubset U ⊔ inSubset V := by
  simp only [small, binaryCover, iSup_bool_eq, Bool.cond_true, Bool.cond_false]

def smallUnionHomologyIso (U V : Set X) (n : ℕ) :
    (chains (binaryCover U V)).homology n ≅
      (inSubset U ⊔ inSubset V : (singularSet X).Subcomplex).toSSet.homology
        (ModuleCat.of ℝ ℝ) n :=
  (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso
    (eqToIso (congrArg SSet.Subcomplex.toSSet (small_binaryCover U V)))

def intersectionHomologyIso (U V : Set X) (n : ℕ) :
    RealSingularHomology n ↥(U ∩ V) ≅
      (inSubset U ⊓ inSubset V : (singularSet X).Subcomplex).toSSet.homology
        (ModuleCat.of ℝ ℝ) n :=
  subspaceHomologyIso (U ∩ V) n ≪≫
    (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).mapIso
      (eqToIso (congrArg SSet.Subcomplex.toSSet (inSubset_inter U V)))

def connecting (U V : Set X) (n : ℕ) :
    (chains (binaryCover U V)).homology (n + 1) ⟶
      RealSingularHomology n ↥(U ∩ V) :=
  (smallUnionHomologyIso U V (n + 1)).hom ≫
    SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n ≫
      (intersectionHomologyIso U V n).inv

theorem member_homology_isZero (U : Set X) [ContractibleSpace U]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((inSubset U).toSSet.homology (ModuleCat.of ℝ ℝ) n) :=
  ModuleCat.isZero_iff_subsingleton.mpr (subspace_homology_subsingleton U n hn)

theorem connecting_injective (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    Function.Injective (connecting U V n) := by
  exact (intersectionHomologyIso U V n).toLinearEquiv.symm.injective.comp
    ((SimplicialMayerVietoris.connecting_injective (inSubset U) (inSubset V) n
      (member_homology_isZero U (n + 1) (Nat.succ_ne_zero n))
      (member_homology_isZero V (n + 1) (Nat.succ_ne_zero n))).comp
        (smallUnionHomologyIso U V (n + 1)).toLinearEquiv.injective)

def connectingIso (U V : Set X) [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0) :
    (chains (binaryCover U V)).homology (n + 1) ≅ RealSingularHomology n ↥(U ∩ V) :=
  smallUnionHomologyIso U V (n + 1) ≪≫
    SimplicialMayerVietoris.connectingIso (inSubset U) (inSubset V) n
      (member_homology_isZero U (n + 1) (Nat.succ_ne_zero n))
      (member_homology_isZero V (n + 1) (Nat.succ_ne_zero n))
      (member_homology_isZero U n hn) (member_homology_isZero V n hn) ≪≫
        (intersectionHomologyIso U V n).symm

@[simp] theorem connectingIso_hom (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    (connectingIso U V n hn).hom = connecting U V n := rfl

def singularConnectingIsoOfQuasiIsoAt (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)] :
    RealSingularHomology (n + 1) X ≅ RealSingularHomology n ↥(U ∩ V) :=
  (asIso (HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1))).symm ≪≫
    connectingIso U V n hn

@[reassoc] theorem inclusion_singularConnectingIsoOfQuasiIsoAt
    (U V : Set X) [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)] :
    HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1) ≫
      (singularConnectingIsoOfQuasiIsoAt U V n hn).hom = connecting U V n := by
  unfold singularConnectingIsoOfQuasiIsoAt
  erw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsIso.hom_inv_id,
    Category.id_comp]
  rfl

end SmallCoverMayerVietoris
end Problem340

end

end OAI
