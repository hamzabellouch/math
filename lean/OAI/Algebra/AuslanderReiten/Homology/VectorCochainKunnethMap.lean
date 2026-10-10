import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunnethNaturality
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorComplex

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)
variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev Diagonal (n : ℕ) := ExternalTensor.Diagonal n

def totalTermCoordinates (n : ℕ) :
    (mapBifunctor P Q T (.up ℕ)).X n ≃ₗ[k]
      (∀ p : Diagonal n, P.X p.val.1 ⊗[k] Q.X p.val.2) :=
  (ModuleCat.coprodIsoDirectSum (fun p : Diagonal n =>
    ((T).obj (P.X p.val.1)).obj (Q.X p.val.2))).toLinearEquiv.trans
      DFinsupp.linearEquivFunOnFintype

theorem totalTermCoordinates_inclusion (i j n : ℕ) (h : i+j=n)
    (x : P.X i ⊗[k] Q.X j) :
    totalTermCoordinates k P Q n ((ιMapBifunctor P Q T (.up ℕ) i j n h).hom x) =
      Pi.single ⟨(i,j),h⟩ x := by
  have hi := ModuleCat.ι_coprodIsoDirectSum_hom
    (fun p : Diagonal n => ((T).obj (P.X p.val.1)).obj (Q.X p.val.2)) ⟨(i,j),h⟩
  exact congrArg (fun y => DFinsupp.linearEquivFunOnFintype (R := k) y)
    (congrArg (fun f => f.hom x) hi)

variable {P Q} {P' Q' : CochainComplex (ModuleCat.{u} k) ℕ}

def diagonalTermMap (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    (∀ p : Diagonal n, P.X p.val.1 ⊗[k] Q.X p.val.2) →ₗ[k]
      (∀ p : Diagonal n, P'.X p.val.1 ⊗[k] Q'.X p.val.2) where
  toFun x p := TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' a x := by
    funext p
    exact (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom).map_smul a (x p)

theorem diagonalTermMap_single (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (p : Diagonal n) (x : P.X p.val.1 ⊗[k] Q.X p.val.2) :
    diagonalTermMap k f g n (Pi.single p x) =
      Pi.single p (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom x) := by
  classical
  funext r
  by_cases h : r=p
  · subst r
    simp only [diagonalTermMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same]
  · simp only [diagonalTermMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_of_ne h,
      map_zero]

theorem totalTermCoordinates_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (x : (mapBifunctor P Q T (.up ℕ)).X n) :
    totalTermCoordinates k P' Q' n (((mapBifunctorMap f g T (.up ℕ)).f n).hom x) =
      diagonalTermMap k f g n (totalTermCoordinates k P Q n x) := by
  have hh : (mapBifunctorMap f g T (.up ℕ)).f n ≫
      ModuleCat.ofHom (totalTermCoordinates k P' Q' n).toLinearMap =
    ModuleCat.ofHom ((diagonalTermMap k f g n).comp
      (totalTermCoordinates k P Q n).toLinearMap) := by
    apply mapBifunctor.hom_ext
    intro i j hij
    erw [← Category.assoc, ι_mapBifunctorMap]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change totalTermCoordinates k P' Q' n
      ((ιMapBifunctor P' Q' T (.up ℕ) i j n hij).hom
        (TensorProduct.map LinearMap.id (g.f j).hom
          (TensorProduct.map (f.f i).hom LinearMap.id z))) =
      diagonalTermMap k f g n (totalTermCoordinates k P Q n
        ((ιMapBifunctor P Q T (.up ℕ) i j n hij).hom z))
    rw [TensorProduct.map_map]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
    rw [totalTermCoordinates_inclusion, totalTermCoordinates_inclusion,
      diagonalTermMap_single]
  exact congrArg (fun a => a.hom x) hh

def homologyCoordinates (n : ℕ) :
    (mapBifunctor P Q T (.up ℕ)).homology n ≃ₗ[k]
      (∀ p : Diagonal n, P.homology p.val.1 ⊗[k] Q.homology p.val.2) :=
  (kunnethIso k T P Q n).toLinearEquiv.trans
    (totalTermCoordinates k (gradedHomology k P) (gradedHomology k Q) n)

theorem homologyCoordinates_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (x : (mapBifunctor P Q T (.up ℕ)).homology n) :
    homologyCoordinates k n ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x) =
      diagonalTermMap k (gradedMap k f) (gradedMap k g) n (homologyCoordinates k n x) := by
  have hn := congrArg (fun a => a.hom x) (kunnethIso_natural k T f g n)
  change (kunnethIso k T P' Q' n).hom.hom
      ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x) =
    ((mapBifunctorMap (gradedMap k f) (gradedMap k g) T (.up ℕ)).f n).hom
      ((kunnethIso k T P Q n).hom.hom x) at hn
  change totalTermCoordinates k (gradedHomology k P') (gradedHomology k Q') n
    ((kunnethIso k T P' Q' n).hom.hom
      ((homologyMap (mapBifunctorMap f g T (.up ℕ)) n).hom x)) = _
  rw [hn]
  exact totalTermCoordinates_natural k (gradedMap k f) (gradedMap k g) n _

end ArExplicit.VectorCochain

end

end OAI
