import Mathlib
import OAI.GroupTheory.FiniteType.CosetInduction

namespace OAI

noncomputable section
open CategoryTheory
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace SemilinearCoinvariants
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) {A : Rep R G} {B : Rep R H}

def tensorNatTrans (α : A ⟶ Rep.res φ B) :
    Rep.resFunctor φ ⋙ (Rep.coinvariantsTensor R G).obj A ⟶
      (Rep.coinvariantsTensor R H).obj B :=
  (Rep.coinvariantsTensorIndNatIso φ A).inv ≫
    (Rep.coinvariantsTensor R H).map ((Rep.indResHomEquiv φ A B).symm α)

lemma tensorNatTrans_mk_tmul (α : A ⟶ Rep.res φ B) (Q : Rep R H)
    (a : A) (q : Q) :
    (tensorNatTrans φ α).app Q (Coinvariants.mk _ (a ⊗ₜ[R] q)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] q) := by
  simp [tensorNatTrans,Rep.coinvariantsTensorIndInv,Rep.coinvariantsTensorMk,
    Rep.indResHomEquiv]

variable (P : ChainComplex (Rep R G) ℕ) (Q : ChainComplex (Rep R H) ℕ)

def chainMap (α : A ⟶ Rep.res φ B)
    (β : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q) :
    P.coinvariantsTensorObj A ⟶ Q.coinvariantsTensorObj B :=
  (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).map β ≫
    (NatTrans.mapHomologicalComplex (tensorNatTrans φ α) _).app Q

lemma chainMap_f_mk_tmul (α : A ⟶ Rep.res φ B)
    (β : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q) (n : ℕ)
    (a : A) (p : P.X n) :
    (chainMap φ P Q α β).f n (Coinvariants.mk _ (a ⊗ₜ[R] p)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] β.f n p) := by
  change (tensorNatTrans φ α).app (Q.X n)
    ((((Rep.coinvariantsTensor R G).obj A).map (β.f n))
      (Coinvariants.mk _ (a ⊗ₜ[R] p))) = _
  change (tensorNatTrans φ α).app (Q.X n)
    (Coinvariants.mk _ (a ⊗ₜ[R] β.f n p)) = _
  exact tensorNatTrans_mk_tmul φ α (Q.X n) a (β.f n p)

def chainMapHomotopy (α : A ⟶ Rep.res φ B)
    {β γ : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q} (h : Homotopy β γ) :
    Homotopy (chainMap φ P Q α β) (chainMap φ P Q α γ) :=
  ((((Rep.coinvariantsTensor R G).obj A).mapHomotopy h).compRight
    ((NatTrans.mapHomologicalComplex (tensorNatTrans φ α) _).app Q))

end SemilinearCoinvariants

namespace CosetEndpoint
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t = t*(f s : G))

include ht in
lemma inv_mul_subtype (s : S) : t⁻¹*(s : G) = (f s : G)*t⁻¹ := by
  have h := congrArg (fun x : G => t⁻¹*x*t⁻¹) (ht s)
  simpa only [mul_assoc,mul_inv_cancel,mul_one,inv_mul_cancel_left] using h

def shiftCoeff : Rep.res S.subtype A ⟶ Rep.res f (Rep.res S.subtype A) :=
  Rep.ofHom ⟨A.ρ t⁻¹,by
    intro s
    change (A.ρ t⁻¹).comp (A.ρ s) = (A.ρ (f s)).comp (A.ρ t⁻¹)
    change A.ρ t⁻¹ * A.ρ s = A.ρ (f s) * A.ρ t⁻¹
    rw [← map_mul,← map_mul,inv_mul_subtype S f t ht]⟩

def shiftChain :
    (Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A) ⟶
      (Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A) :=
  SemilinearCoinvariants.chainMap f _ _ (shiftCoeff S A f t ht)
    (StandardVertex.chainMap f f (by intro s u; exact f.map_mul s u))

def baseShiftCoeff : Rep.res S.subtype A ⟶
    Rep.res (S.subtype.comp f) (CosetInduction.cosetRep S A) :=
  shiftCoeff S A f t ht ≫ (Rep.resFunctor f).map (CosetInduction.baseHom S A)

@[simp] lemma baseShiftCoeff_apply (a : A) :
    baseShiftCoeff S A f t ht a =
      Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) := rfl

include ht in
lemma leftVertex_equivariant (s u : S) :
    t⁻¹*((s*u : S) : G) = (S.subtype.comp f) s * (t⁻¹*(u : G)) := by
  change t⁻¹*((s : G)*(u : G)) = _
  rw [← mul_assoc, inv_mul_subtype S f t ht, mul_assoc]
  rfl

def leftVertexMap := StandardVertex.chainMap (R := R) (S.subtype.comp f)
  (fun s : S => t⁻¹*(s : G)) (leftVertex_equivariant S f t ht)

def rightVertexMap := StandardVertex.chainMap (R := R) (S.subtype.comp f)
  (S.subtype.comp f) (by intro s u; exact (S.subtype.comp f).map_mul s u)

def leftChain := SemilinearCoinvariants.chainMap (S.subtype.comp f)
  (Rep.standardComplex R S) (Rep.standardComplex R G)
  (baseShiftCoeff S A f t ht) (leftVertexMap (R := R) S f t ht)

def rightChain := SemilinearCoinvariants.chainMap (S.subtype.comp f)
  (Rep.standardComplex R S) (Rep.standardComplex R G)
  (baseShiftCoeff S A f t ht) (rightVertexMap (R := R) S f)

def endpointHomotopy : Homotopy (leftChain S A f t ht) (rightChain S A f t ht) :=
  SemilinearCoinvariants.chainMapHomotopy (S.subtype.comp f) _ _
    (baseShiftCoeff S A f t ht)
    (StandardVertex.homotopy (S.subtype.comp f) _ (leftVertex_equivariant S f t ht)
      _ (by intro s u; exact (S.subtype.comp f).map_mul s u))

end CosetEndpoint

namespace StandardTensor
section
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] {A B : Rep R G}

def coefficientMap (α : A ⟶ B) :
    (Rep.standardComplex R G).coinvariantsTensorObj A ⟶
      (Rep.standardComplex R G).coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).app _

@[simp] lemma coefficientMap_f_mk_tmul (α : A ⟶ B) (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → G)) :
    (coefficientMap α).f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] z) := rfl

lemma chain_ext {Q : ChainComplex (ModuleCat R) ℕ}
    {u v : (Rep.standardComplex R G).coinvariantsTensorObj A ⟶ Q}
    (h : ∀ (n : ℕ) (a : A) (s : Fin (n+1) → G),
      u.f n (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
      v.f n (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1))) : u=v := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  exact h n a s

end

open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G H : Type} [CommRing R] [Group G] [Group H]

lemma semilinear_single (φ : G →* H) {A : Rep R G} {B : Rep R H}
    (α : A ⟶ Rep.res φ B) (v : G → H) (hv : ∀ g x, v (g*x)=φ g*v x)
    (n : ℕ) (a : A) (s : Fin (n+1) → G) :
    (SemilinearCoinvariants.chainMap φ (Rep.standardComplex R G) (Rep.standardComplex R H)
      α (StandardVertex.chainMap φ v hv)).f n
      (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
        Coinvariants.mk (B.ρ.tprod (Rep.diagonal R H (n+1)).ρ) ((α a : B) ⊗ₜ[R] MonoidAlgebra.single (v ∘ s) 1) := by
  exact (SemilinearCoinvariants.chainMap_f_mk_tmul φ _ _ α
    (StandardVertex.chainMap φ v hv) n a (MonoidAlgebra.single s 1)).trans
      (congrArg (fun z : MonoidAlgebra R (Fin (n+1) → H) => Coinvariants.mk (B.ρ.tprod (Rep.diagonal R H (n+1)).ρ) ((α a : B) ⊗ₜ[R] z))
        (StandardVertex.map_single φ v hv n s 1))

lemma shapiro_single (S : Subgroup G) (A : Rep R G) (n : ℕ) (a : A) (s : Fin (n+1) → S) :
    (StandardShapiro.cosetEquiv S A).hom.f n
      (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
        Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ) ((Finsupp.single (QuotientGroup.mk (1 : G)) a : CosetInduction.cosetRep S A) ⊗ₜ[R]
          MonoidAlgebra.single (S.subtype ∘ s) 1) := by
  exact (StandardShapiro.cosetEquiv_hom_f_mk_tmul S A n a (MonoidAlgebra.single s 1)).trans
    (congrArg (fun z : MonoidAlgebra R (Fin (n+1) → G) =>
      Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
        (Finsupp.single (QuotientGroup.mk (1 : G)) a ⊗ₜ[R] z))
        (StandardVertex.map_single S.subtype S.subtype (by intro g x; rfl) n s 1))

end StandardTensor

namespace CosetEndpoint
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t = t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v) = g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

include pbase in
lemma shapiro_parent_eq_left :
    (StandardShapiro.cosetEquiv S A).hom ≫
      StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq) =
        leftChain S A f t ht := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg
    (fun x => (StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq)).f n x)
    (StandardTensor.shapiro_single S A n a s)
  have h₂ := StandardTensor.coefficientMap_f_mk_tmul (FunctionalTree.parentHom A p peq) n
    (Finsupp.single (QuotientGroup.mk (1 : G)) a)
    (MonoidAlgebra.single (S.subtype ∘ s) 1)
  have h₃ := StandardTensor.semilinear_single (S.subtype.comp f)
    (baseShiftCoeff S A f t ht) (fun s : S => t⁻¹*(s : G))
    (leftVertex_equivariant S f t ht) n a s
  apply (h₁.trans h₂).trans
  apply Eq.trans _ h₃.symm
  change Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
    (FunctionalTree.parentMap p
      (Finsupp.single (QuotientGroup.mk (1 : G)) a) ⊗ₜ[R]
    MonoidAlgebra.single (S.subtype ∘ s) 1) =
    Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
      (Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) ⊗ₜ[R]
      MonoidAlgebra.single ((fun s : S => t⁻¹*(s : G)) ∘ s) 1)
  rw [FunctionalTree.parentMap_single,pbase]
  have h := Coinvariants.mk_self_apply
    ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ) t⁻¹
    (Finsupp.single (QuotientGroup.mk t) a ⊗ₜ[R]
      MonoidAlgebra.single (S.subtype ∘ s) 1)
  have hact : ((CosetInduction.cosetRep S A).ρ.tprod
      (Rep.diagonal R G (n+1)).ρ) t⁻¹
      (Finsupp.single (QuotientGroup.mk t) a ⊗ₜ[R]
        MonoidAlgebra.single (S.subtype ∘ s) 1) =
      Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) ⊗ₜ[R]
        MonoidAlgebra.single ((fun s : S => t⁻¹*(s : G)) ∘ s) 1 := by
    change (FunctionalTree.diagonalRep A).ρ t⁻¹
        (Finsupp.single (QuotientGroup.mk t) a) ⊗ₜ[R]
        (Rep.diagonal R G (n+1)).ρ t⁻¹
        (MonoidAlgebra.single (S.subtype ∘ s) 1) = _
    rw [FunctionalTree.diagonalRep_single]
    simp only [MulAction.Quotient.smul_mk,smul_eq_mul,inv_mul_cancel]
    change _ ⊗ₜ[R] Representation.ofMulAction R G (Fin (n+1) → G) t⁻¹
      (MonoidAlgebra.single (S.subtype ∘ s) 1) = _
    rw [Representation.ofMulAction_single]
    rfl
  rw [hact] at h
  exact h.symm

lemma shift_shapiro_eq_right :
    shiftChain S A f t ht ≫ (StandardShapiro.cosetEquiv S A).hom =
      rightChain S A f t ht := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg (fun x => (StandardShapiro.cosetEquiv S A).hom.f n x)
    (StandardTensor.semilinear_single f (shiftCoeff S A f t ht) f
      (by intro g x; exact f.map_mul g x) n a s)
  have h₂ := StandardTensor.shapiro_single S A n (A.ρ t⁻¹ a) (f ∘ s)
  have h₃ := StandardTensor.semilinear_single (S.subtype.comp f)
    (baseShiftCoeff S A f t ht) (S.subtype.comp f)
    (by intro g x; exact (S.subtype.comp f).map_mul g x) n a s
  exact (h₁.trans h₂).trans h₃.symm

def shapiroParentHomotopy : Homotopy
    ((StandardShapiro.cosetEquiv S A).hom ≫
      StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq))
    (shiftChain S A f t ht ≫ (StandardShapiro.cosetEquiv S A).hom) := by
  rw [shapiro_parent_eq_left S A f t ht p peq pbase,shift_shapiro_eq_right]
  exact endpointHomotopy S A f t ht

end CosetEndpoint

end

end OAI
