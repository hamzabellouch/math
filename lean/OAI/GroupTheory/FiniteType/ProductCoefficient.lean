import Mathlib
import OAI.GroupTheory.FiniteType.UniformProductSupport

namespace OAI

noncomputable section
namespace ProductCoefficient
variable (G I C : Type*) [Group G]

abbrev Module := I → (C × G →₀ ℤ)

def rightShift (g : G) : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,p.2*g⁻¹))

@[simp] lemma rightShift_single (g : G) (c : C) (u : G) (r : ℤ) :
    rightShift G C g (Finsupp.single (c,u) r) = Finsupp.single (c,u*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift G C 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  rintro ⟨c,u⟩ r
  simp

lemma rightShift_mul (g h : G) :
    rightShift G C (g*h) = (rightShift G C g).comp (rightShift G C h) := by
  apply Finsupp.lhom_ext
  rintro ⟨c,u⟩ r
  simp [mul_assoc]

def representation : Representation ℤ G (Module G I C) where
  toFun g := LinearMap.pi (fun i => (rightShift G C g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro z
    funext i
    exact congrArg (fun f : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) => f (z i)) (rightShift_one G C)
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    funext i
    exact congrArg (fun f : (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) => f (z i)) (rightShift_mul G C g h)

@[simp] lemma representation_apply (g : G) (z : Module G I C) (i : I) :
    representation G I C g z i = rightShift G C g (z i) := rfl

abbrev rep : Rep ℤ G := Rep.of (representation G I C)

end ProductCoefficient

namespace ListChains
section
variable (G C : Type*) [Group G]

def place : (C × G →₀ ℤ) →ₗ[ℤ] (Chain G →ₗ[ℤ] (C →₀ Chain G)) :=
  Finsupp.linearCombination ℤ
    (fun p : C × G => (Finsupp.lsingle p.1).comp (mapChain G (fun x => p.2*x)))

@[simp] lemma place_single (c : C) (u : G) (r : ℤ) (z : Chain G) :
    place G C (Finsupp.single (c,u) r) z =
      r • Finsupp.single c (mapChain G (fun x => u*x) z) := by
  simp [place]

lemma boundary_place (a : C × G →₀ ℤ) (z : Chain G) :
    cosetBoundary G (place G C a z) = place G C a (boundary G z) := by
  have h : (cosetBoundary G).comp ((place G C).flip z) =
      (place G C).flip (boundary G z) := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      cosetBoundary_single,boundary_mapChain]
  exact LinearMap.congr_fun h a

lemma place_rightShift_translate (a : C × G →₀ ℤ) (z : Chain G) (g : G) :
    place G C (ProductCoefficient.rightShift G C g a)
      (mapChain G (fun x => g*x) z) = place G C a z := by
  have h : ((place G C).flip (mapChain G (fun x => g*x) z)).comp
      (ProductCoefficient.rightShift G C g) = (place G C).flip z := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,
      ProductCoefficient.rightShift_single,place_single,mapChain_comp]
    congr 3
    apply congrArg (mapChain G)
    funext x
    simp [mul_assoc]
  exact LinearMap.congr_fun h a

end

section
variable (G I C : Type*) [Group G]

@[simp] lemma shapeCoordinates_single (c : C) (s : Simplex G) (r : ℤ) :
    shapeCoordinates G C (Finsupp.single c (Finsupp.single s r)) =
      Finsupp.single (relativeType G s) (Finsupp.single (c,s.1) r) := by
  classical
  simp [shapeCoordinates,shapeBasisEquiv]

lemma shapeCoordinates_place_one (a : C × G →₀ ℤ) (l : List G) :
    shapeCoordinates G C (place G C a (Finsupp.single (1,l) 1)) = Finsupp.single l a := by
  have h : (shapeCoordinates G C).toLinearMap.comp
      ((place G C).flip (Finsupp.single (1,l) 1)) = Finsupp.lsingle l := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      mapChain_single]
    simp [relativeType,List.map_map,Finsupp.smul_single]
  exact LinearMap.congr_fun h a

lemma productTupleEquiv_single_val (n : ℕ) (s : Fin n → G)
    (a : CoefficientProduct G I C) :
    (productTupleEquiv G I C n (Finsupp.single s a)).val =
      realizeShapes G I C (Finsupp.single (List.ofFn s) a) := by
  classical
  change realizeShapes G I C
    (((Finsupp.supportedEquivFinsupp (R := ℤ) (M := CoefficientProduct G I C) {l : List G | l.length = n}).symm
      ((Finsupp.lcongr (tupleShapeEquiv G n) (LinearEquiv.refl ℤ _))
        (Finsupp.single s a))).val) = _
  rw [Finsupp.lcongr_single,Finsupp.supportedEquivFinsupp_symm_single]
  rfl

lemma productTupleEquiv_single_place (n : ℕ) (s : Fin n → G)
    (a : CoefficientProduct G I C) (i : I) :
    (productTupleEquiv G I C n (Finsupp.single s a)).val i =
      place G C (a i) (Finsupp.single (1,List.ofFn s) 1) := by
  apply (shapeCoordinates G C).injective
  rw [productTupleEquiv_single_val,shapeCoordinates_realize,shapeCoordinates_place_one]
  simp [UniformProductSupport.evaluate]

end

variable (G : Type*)

def tupleBasisEquiv (n : ℕ) : (Fin (n+1) → G) ≃ {s : Simplex G // degree G s = n} where
  toFun c := ⟨(c 0,List.ofFn (fun i : Fin n => c i.succ)),List.length_ofFn⟩
  invFun s := Fin.cons s.val.1 (fun i => s.val.2.get ⟨i.val,by have hs : s.val.2.length = n := s.property; omega⟩)
  left_inv := by
    intro c
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    rintro ⟨⟨g,l⟩,hl⟩
    apply Subtype.ext
    change (g,List.ofFn (fun i : Fin n => l.get ⟨i.val,_⟩)) = (g,l)
    have he : n = l.length := hl.symm
    subst n
    exact congrArg (fun l => (g,l)) List.ofFn_getElem

def tupleChainEquiv (n : ℕ) : ((Fin (n+1) → G) →₀ ℤ) ≃ₗ[ℤ] degreeModule G n :=
  (Finsupp.lcongr (tupleBasisEquiv G n) (LinearEquiv.refl ℤ ℤ)).trans
    (Finsupp.supportedEquivFinsupp {s : Simplex G | degree G s = n}).symm

@[simp] lemma tupleChainEquiv_single (n : ℕ) (c : Fin (n+1) → G) (r : ℤ) :
    (tupleChainEquiv G n (Finsupp.single c r)).val =
      Finsupp.single (c 0,List.ofFn (fun i : Fin n => c i.succ)) r := by
  change ((Finsupp.supportedEquivFinsupp {s : Simplex G | degree G s = n}).symm
    ((Finsupp.lcongr (tupleBasisEquiv G n) (LinearEquiv.refl ℤ ℤ)) (Finsupp.single c r))).val = _
  rw [Finsupp.lcongr_single,Finsupp.supportedEquivFinsupp_symm_single]
  rfl

def fromTuples (n : ℕ) : ((Fin (n+1) → G) →₀ ℤ) →ₗ[ℤ] Chain G :=
  (degreeModule G n).subtype.comp (tupleChainEquiv G n).toLinearMap

@[simp] lemma fromTuples_single (n : ℕ) (c : Fin (n+1) → G) (r : ℤ) :
    fromTuples G n (Finsupp.single c r) =
      Finsupp.single (c 0,List.ofFn (fun i : Fin n => c i.succ)) r :=
  tupleChainEquiv_single G n c r

lemma fromTuples_injective (n : ℕ) : Function.Injective (fromTuples G n) :=
  Subtype.val_injective.comp (tupleChainEquiv G n).injective

lemma fromTuples_range (n : ℕ) : LinearMap.range (fromTuples G n) = degreeModule G n := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact (tupleChainEquiv G n x).property
  · intro hz
    exact ⟨(tupleChainEquiv G n).symm ⟨z,hz⟩,congrArg Subtype.val ((tupleChainEquiv G n).apply_symm_apply _)⟩

end ListChains

open CategoryTheory
namespace RelativeStandardFree
variable (k G : Type) [CommRing k] [Group G]

def basisEquiv (n : ℕ) : (Fin (n+1) → G) ≃ ((Fin n → G) × G) where
  toFun c := (fun i => (c 0)⁻¹ * c i.succ, c 0)
  invFun p := Fin.cons p.2 (fun i => p.2 * p.1 i)
  left_inv := by
    intro c
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    rintro ⟨s,g⟩
    simp

def linearEquiv (n : ℕ) : MonoidAlgebra k (Fin (n+1) → G) ≃ₗ[k]
    ((Fin n → G) →₀ MonoidAlgebra k G) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.lcongr (basisEquiv G n) (LinearEquiv.refl k k)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp] lemma linearEquiv_single (n : ℕ) (c : Fin (n+1) → G) (r : k) :
    linearEquiv k G n (MonoidAlgebra.single c r) =
      Finsupp.single (fun i => (c 0)⁻¹*c i.succ) (MonoidAlgebra.single (c 0) r) := by
  simp [linearEquiv,basisEquiv]

lemma linearEquiv_intertwines (n : ℕ) (g : G) :
    (linearEquiv k G n).toLinearMap.comp ((Rep.diagonal k G (n+1)).ρ g) =
      ((Rep.free k G (Fin n → G)).ρ g).comp (linearEquiv k G n).toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change linearEquiv k G n ((Representation.diagonal k G (n+1)) g
      (MonoidAlgebra.single c 1)) = (Representation.free k G (Fin n → G)) g
      (linearEquiv k G n (MonoidAlgebra.single c 1))
  rw [Representation.ofMulAction_single,linearEquiv_single,linearEquiv_single,
    Representation.free_single_single]
  congr 1
  funext i
  simp [mul_assoc]

def repIso (n : ℕ) : Rep.diagonal k G (n+1) ≅ Rep.free k G (Fin n → G) :=
  Rep.mkIso (Representation.Equiv.mk (linearEquiv k G n) (linearEquiv_intertwines k G n))

@[simp] lemma repIso_hom_single (n : ℕ) (c : Fin (n+1) → G) (r : k) :
    (repIso k G n).hom.hom (MonoidAlgebra.single c r) =
      Finsupp.single (fun i => (c 0)⁻¹*c i.succ) (MonoidAlgebra.single (c 0) r) :=
  linearEquiv_single k G n c r

end RelativeStandardFree

end

end OAI
