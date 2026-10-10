import Mathlib
import OAI.GroupTheory.FiniteType.SemilinearCoinvariants

namespace OAI

noncomputable section
open CategoryTheory
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace CosetCoordinates
variable {G : Type*} [Group G] (S : Subgroup G)

def equiv : G ≃ (G ⧸ S) × S where
  toFun g := (QuotientGroup.mk g,
    ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g,
      QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk g : G ⧸ S))⟩)
  invFun v := v.1.out*(v.2 : G)
  left_inv g := by simp
  right_inv v := by
    rcases v with ⟨c,s⟩
    have h : (QuotientGroup.mk (c.out*(s : G)) : G ⧸ S) = c :=
      (QuotientGroup.mk_mul_of_mem c.out s.property).trans (Quotient.out_eq' c)
    apply Prod.ext
    · exact h
    · apply Subtype.ext
      change (Quotient.out (QuotientGroup.mk (c.out*(s : G)) : G ⧸ S))⁻¹ *
        (c.out*(s : G)) = (s : G)
      rw [h,inv_mul_cancel_left]

@[simp] lemma equiv_fst (g : G) : (equiv S g).1 = QuotientGroup.mk g := rfl
@[simp] lemma equiv_snd (g : G) : ((equiv S g).2 : G) =
    (Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g := rfl
@[simp] lemma equiv_symm_apply (c : G ⧸ S) (s : S) :
    (equiv S).symm (c,s) = c.out*(s : G) := rfl

lemma equiv_mul_subgroup (g : G) (s : S) :
    equiv S (g*(s : G)) = ((equiv S g).1, (equiv S g).2*s) := by
  have h := QuotientGroup.mk_mul_of_mem g s.property
  apply Prod.ext
  · exact h
  · apply Subtype.ext
    change (Quotient.out (QuotientGroup.mk (g*(s : G)) : G ⧸ S))⁻¹*(g*(s : G)) =
      ((Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g)*(s : G)
    rw [h,mul_assoc]

variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

def nextCoset (c : G ⧸ S) : G ⧸ S := QuotientGroup.mk (c.out*t)
def correction (c : G ⧸ S) : S := (equiv S (c.out*t)).2

include ht in
lemma equiv_mul_stable (g : G) :
    equiv S (g*t) = (nextCoset S t (equiv S g).1,
      correction S t (equiv S g).1 * f (equiv S g).2) := by
  have hg : g = (equiv S g).1.out * ((equiv S g).2 : G) :=
    (equiv S).symm_apply_apply g |>.symm
  have he : g*t = ((equiv S g).1.out*t)*(f (equiv S g).2 : G) := by
    calc
      g*t = ((equiv S g).1.out * ((equiv S g).2 : G))*t := congrArg (·*t) hg
      _ = _ := by rw [mul_assoc,ht,← mul_assoc]
  rw [he, equiv_mul_subgroup]
  rfl

end CosetCoordinates

namespace RegularProduct
section
open CategoryTheory
variable (G I : Type) [Group G]

abbrev Module := I → (G →₀ ℤ)

def rightShift (g : G) : (G →₀ ℤ) →ₗ[ℤ] (G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun x => x*g⁻¹)

@[simp] lemma rightShift_single (g x : G) (r : ℤ) :
    rightShift G g (Finsupp.single x r) = Finsupp.single (x*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift G 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  simp

lemma rightShift_mul (g h : G) :
    rightShift G (g*h) = (rightShift G g).comp (rightShift G h) := by
  apply Finsupp.lhom_ext
  intro x r
  simp [mul_assoc]

def representation : Representation ℤ G (Module G I) where
  toFun g := LinearMap.pi (fun i => (rightShift G g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_one G) (a i)
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_mul G g h) (a i)

abbrev rep : Rep ℤ G := Rep.of (representation G I)

variable (S : Subgroup G)

def coordinateEquiv : Module G I ≃ₗ[ℤ] ProductCoefficient.Module S I (G ⧸ S) :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S))

@[simp] lemma coordinateEquiv_apply (a : Module G I) (i : I) :
    coordinateEquiv G I S a i = Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (a i) := rfl

lemma coordinateEquiv_rightShift (s : S) (a : G →₀ ℤ) :
    Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (rightShift G (s : G) a) =
      ProductCoefficient.rightShift S (G ⧸ S) s (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) a) := by
  have h : (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) : (G →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap.comp
      (rightShift G (s : G)) =
    (ProductCoefficient.rightShift S (G ⧸ S) s).comp
      (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    change Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)
        (rightShift G (s : G) (Finsupp.single x r)) =
      ProductCoefficient.rightShift S (G ⧸ S) s
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (Finsupp.single x r))
    rw [rightShift_single,Finsupp.domLCongr_single,Finsupp.domLCongr_single]
    change Finsupp.single (CosetCoordinates.equiv S (x*(s : G)⁻¹)) r =
      ProductCoefficient.rightShift S (G ⧸ S) s
        (Finsupp.single ((CosetCoordinates.equiv S x).1,(CosetCoordinates.equiv S x).2) r)
    rw [ProductCoefficient.rightShift_single]
    congr 1
    exact CosetCoordinates.equiv_mul_subgroup S x s⁻¹
  exact LinearMap.congr_fun h a

def restrictionIso : Rep.res S.subtype (rep G I) ≅ ProductCoefficient.rep S I (G ⧸ S) :=
  Rep.mkIso (Representation.Equiv.mk (coordinateEquiv G I S) (by
    intro s
    apply LinearMap.ext
    intro a
    funext i
    exact coordinateEquiv_rightShift G S s (a i)))

end

open CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

include ht in
lemma coordinateEquiv_rightStable (a : G →₀ ℤ) :
    Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (rightShift G t⁻¹ a) =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) a) := by
  have h : (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap.comp
      (rightShift G t⁻¹) =
    (ProductCoefficient.affineShift S (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)).comp
      (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    change Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S)
        (rightShift G t⁻¹ (Finsupp.single x r)) =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.domLCongr (R := ℤ) (CosetCoordinates.equiv S) (Finsupp.single x r))
    rw [rightShift_single,Finsupp.domLCongr_single,Finsupp.domLCongr_single,inv_inv]
    change Finsupp.single (CosetCoordinates.equiv S (x*t)) r =
      ProductCoefficient.affineShift S (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (Finsupp.single ((CosetCoordinates.equiv S x).1,(CosetCoordinates.equiv S x).2) r)
    rw [ProductCoefficient.affineShift_single]
    congr 1
    exact CosetCoordinates.equiv_mul_stable S f t ht x
  exact LinearMap.congr_fun h a

include ht in
lemma coordinateEquiv_rep_inv (a : Module G I) :
    coordinateEquiv G I S ((rep G I).ρ t⁻¹ a) =
      ProductCoefficient.productAffineShift S I (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)
        (coordinateEquiv G I S a) := by
  funext i
  exact coordinateEquiv_rightStable G S f t ht (a i)

end RegularProduct

namespace ListChains
open CategoryTheory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]
lemma standardShiftChainMap_mk_tmul (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+1) → G)) :
    (standardShiftChainMap G I C f σ δ).f n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk ((ProductCoefficient.rep G I C).ρ.tprod (Rep.diagonal ℤ G (n+1)).ρ)
        (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ] standardTupleMap G f n z) := by
  rw [standardShiftChainMap_f]
  exact standardShift_mk_tmul G I C f σ δ n a z
end ListChains

namespace RegularProduct
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

def restrictionChainIso :
    (Rep.standardComplex ℤ S).coinvariantsTensorObj (Rep.res S.subtype (rep G I)) ≅
      ListChains.standardProductComplex S I (G ⧸ S) :=
  (NatIso.mapHomologicalComplex
    ((Rep.coinvariantsTensor ℤ S).mapIso (restrictionIso G I S)) _).app _

lemma restrictionChainIso_hom_f (n : ℕ) (a : Module G I)
    (z : MonoidAlgebra ℤ (Fin (n+1) → S)) :
    (restrictionChainIso G I S).hom.f n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk _ (coordinateEquiv G I S a ⊗ₜ[ℤ] z) := rfl

lemma standardTupleMap_single (n : ℕ) (s : Fin (n+1) → S) :
    ListChains.standardTupleMap S f n (MonoidAlgebra.single s 1) =
      MonoidAlgebra.single (f ∘ s) 1 := by
  simp [ListChains.standardTupleMap,ControlledChains.mapChain]

lemma restrictionChainIso_shift :
    CosetEndpoint.shiftChain S (rep G I) f t ht ≫ (restrictionChainIso G I S).hom =
      (restrictionChainIso G I S).hom ≫
      ListChains.standardShiftChainMap S I (G ⧸ S) f
        (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t) := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg (fun q => (restrictionChainIso G I S).hom.f n q)
    (StandardTensor.semilinear_single f (CosetEndpoint.shiftCoeff S (rep G I) f t ht)
      f (by intro s u; exact f.map_mul s u) n a s)
  have h₂ := restrictionChainIso_hom_f G I S n ((rep G I).ρ t⁻¹ a)
    (MonoidAlgebra.single (f ∘ s) 1)
  have h₃ := congrArg
    (fun q => (ListChains.standardShiftChainMap S I (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)).f n q)
    (restrictionChainIso_hom_f G I S n a (MonoidAlgebra.single s 1))
  have h₄ := ListChains.standardShiftChainMap_mk_tmul S I (G ⧸ S) f
    (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t) n
    (coordinateEquiv G I S a) (MonoidAlgebra.single s 1)
  apply (h₁.trans h₂).trans
  apply Eq.trans _ (h₃.trans h₄).symm
  exact congrArg₂
    (fun (b : ProductCoefficient.Module S I (G ⧸ S))
      (z : MonoidAlgebra ℤ (Fin (n+1) → S)) =>
      Coinvariants.mk ((ProductCoefficient.rep S I (G ⧸ S)).ρ.tprod
        (Rep.diagonal ℤ S (n+1)).ρ) (b ⊗ₜ[ℤ] z))
    (coordinateEquiv_rep_inv G I S f t ht a)
    (standardTupleMap_single G S f n s).symm

end RegularProduct

end

end OAI
