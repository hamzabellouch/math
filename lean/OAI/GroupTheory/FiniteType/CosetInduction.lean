import Mathlib
import OAI.GroupTheory.FiniteType.StandardShapiro

namespace OAI

noncomputable section
open CategoryTheory
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
namespace CosetInduction
open CategoryTheory _root_.Representation _root_.OAI.Representation
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)

abbrev cosetRep := FunctionalTree.diagonalRep (V := G ⧸ S) A

lemma subgroup_fixes_base (s : S) :
    (s : G) • (QuotientGroup.mk (1 : G) : G ⧸ S) = QuotientGroup.mk (1 : G) := by
  simp only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one]
  exact QuotientGroup.eq.mpr (by simp)

def baseHom : Rep.res S.subtype A ⟶ Rep.res S.subtype (cosetRep S A) :=
  Rep.ofHom ⟨Finsupp.lsingle (QuotientGroup.mk (1 : G)),by
    intro s
    apply LinearMap.ext
    intro a
    change Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ s a) =
      (cosetRep S A).ρ s (Finsupp.single (QuotientGroup.mk (1 : G)) a)
    rw [FunctionalTree.diagonalRep_single,subgroup_fixes_base]⟩

def indToCosets : Rep.ind S.subtype (Rep.res S.subtype A) ⟶ cosetRep S A :=
  (Rep.indResHomEquiv S.subtype (Rep.res S.subtype A) (cosetRep S A)).symm (baseHom S A)

lemma indToCosets_mk (h : G) (a : A) :
    indToCosets S A (IndV.mk S.subtype (Rep.res S.subtype A).ρ h a) =
      Finsupp.single (QuotientGroup.mk h⁻¹) (A.ρ h⁻¹ a) := by
  simp [indToCosets,Rep.indResHomEquiv,baseHom]
  change (cosetRep S A).ρ h⁻¹ (Finsupp.single (QuotientGroup.mk (1 : G)) a) = _
  rw [FunctionalTree.diagonalRep_single]
  simp
  rfl

lemma ind_mk_left (s : S) (h : G) (a : A) :
    IndV.mk S.subtype (Rep.res S.subtype A).ρ ((s : G)*h) (A.ρ s a) =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ h a := by
  have H := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular R G).comp S.subtype) (Rep.res S.subtype A).ρ)
    s (MonoidAlgebra.single h (1 : R) ⊗ₜ[R] a)
  simpa using H

def cosetSection : (G ⧸ S) → A →ₗ[R] Representation.IndV S.subtype (Rep.res S.subtype A).ρ :=
  Quotient.lift (fun h => (IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹).comp (A.ρ h⁻¹)) (by
    intro h k hrel
    let s : S := ⟨h⁻¹*k,QuotientGroup.leftRel_apply.mp hrel⟩
    have hk : k = h*(s : G) := by change k = h*(h⁻¹*k); group
    apply LinearMap.ext
    intro a
    change IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹ (A.ρ h⁻¹ a) =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ k⁻¹ (A.ρ k⁻¹ a)
    rw [hk,mul_inv_rev,map_mul,Module.End.mul_apply]
    exact (ind_mk_left S A s⁻¹ h⁻¹ (A.ρ h⁻¹ a)).symm)

@[simp] lemma cosetSection_mk (h : G) (a : A) :
    cosetSection S A (QuotientGroup.mk h) a =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹ (A.ρ h⁻¹ a) := rfl

def cosetsToInd : ((G ⧸ S) →₀ A) →ₗ[R] Representation.IndV S.subtype (Rep.res S.subtype A).ρ :=
  Finsupp.lsum R (cosetSection S A)

@[simp] lemma cosetsToInd_single (v : G ⧸ S) (a : A) :
    cosetsToInd S A (Finsupp.single v a) = cosetSection S A v a := by
  simp [cosetsToInd]

lemma cosetsToInd_indToCosets :
    (cosetsToInd S A).comp (indToCosets S A).hom.toLinearMap = LinearMap.id := by
  apply IndV.hom_ext
  intro h
  apply LinearMap.ext
  intro a
  change cosetsToInd S A (indToCosets S A (IndV.mk S.subtype (Rep.res S.subtype A).ρ h a)) =
    IndV.mk S.subtype (Rep.res S.subtype A).ρ h a
  rw [indToCosets_mk,cosetsToInd_single,cosetSection_mk,inv_inv]
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
  rfl

lemma indToCosets_cosetsToInd :
    (indToCosets S A).hom.toLinearMap.comp (cosetsToInd S A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  induction v using Quotient.inductionOn with
  | h h =>
    change indToCosets S A (cosetsToInd S A (Finsupp.single (QuotientGroup.mk h) a)) =
      Finsupp.single (QuotientGroup.mk h) a
    rw [cosetsToInd_single,cosetSection_mk,indToCosets_mk,inv_inv]
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl

def indCosetIso : Rep.ind S.subtype (Rep.res S.subtype A) ≅ cosetRep S A := by
  letI : Mono (indToCosets S A) := (Rep.mono_iff_injective _).mpr (by
    intro x y h
    have hx := LinearMap.congr_fun (cosetsToInd_indToCosets S A) x
    have hy := LinearMap.congr_fun (cosetsToInd_indToCosets S A) y
    change cosetsToInd S A (indToCosets S A x) = x at hx
    change cosetsToInd S A (indToCosets S A y) = y at hy
    exact hx.symm.trans ((congrArg (cosetsToInd S A) h).trans hy))
  letI : Epi (indToCosets S A) := (Rep.epi_iff_surjective _).mpr (by
    intro y
    refine ⟨cosetsToInd S A y,?_⟩
    exact LinearMap.congr_fun (indToCosets_cosetsToInd S A) y)
  letI := CategoryTheory.isIso_of_mono_of_epi (indToCosets S A)
  exact CategoryTheory.asIso (indToCosets S A)

end CosetInduction

namespace StandardShapiro
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)

def cosetCoefficientIso :
    (Rep.standardComplex R G).coinvariantsTensorObj (Rep.ind S.subtype (Rep.res S.subtype A)) ≅
      (Rep.standardComplex R G).coinvariantsTensorObj (CosetInduction.cosetRep S A) :=
  (NatIso.mapHomologicalComplex
    ((Rep.coinvariantsTensor R G).mapIso (CosetInduction.indCosetIso S A)) _).app _

def cosetEquiv :
    HomotopyEquiv ((Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A))
      ((Rep.standardComplex R G).coinvariantsTensorObj (CosetInduction.cosetRep S A)) :=
  (indEquiv S (Rep.res S.subtype A)).trans (HomotopyEquiv.ofIso (cosetCoefficientIso S A))

lemma cosetEquiv_hom_f_mk_tmul (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → S)) :
    (cosetEquiv S A).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (Finsupp.single (QuotientGroup.mk (1 : G)) a ⊗ₜ[R]
        StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z) := by
  change (cosetCoefficientIso S A).hom.f n
    ((indEquiv S (Rep.res S.subtype A)).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z))) = _
  rw [indEquiv_hom_f_mk_tmul]
  change Coinvariants.mk _ (CosetInduction.indToCosets S A
    (IndV.mk S.subtype (Rep.res S.subtype A).ρ 1 a) ⊗ₜ[R] _) = _
  rw [CosetInduction.indToCosets_mk]
  simp only [inv_one,map_one,Module.End.one_apply]
  rfl

end StandardShapiro

open CategoryTheory CategoryTheory.Limits
namespace ExactTargetHomotopy
variable {C : Type*} [Category* C] [Abelian C]
  {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] {Z : C}
variable (ε : Q.X 0 ⟶ Z) (hε : Q.d 1 0 ≫ ε = 0)
  (h0 : (ShortComplex.mk (Q.d 1 0) ε hε).Exact)
  (hs : ∀ n, (ShortComplex.mk (Q.d (n+2) (n+1)) (Q.d (n+1) n)
    (Q.d_comp_d (n+2) (n+1) n)).Exact)
variable (f : P ⟶ Q) (comm : f.f 0 ≫ ε = 0)

def stepZero : P.X 0 ⟶ Q.X 1 := h0.liftFromProjective (f.f 0) comm

@[reassoc (attr := simp)]
lemma stepZero_comp : stepZero ε hε h0 f comm ≫ Q.d 1 0 = f.f 0 :=
  h0.liftFromProjective_comp _ _

def stepOne : P.X 1 ⟶ Q.X 2 :=
  (hs 0).liftFromProjective (f.f 1 - P.d 1 0 ≫ stepZero ε hε h0 f comm)
    (by rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.Hom.comm,
      stepZero_comp, sub_self])

@[reassoc (attr := simp)]
lemma stepOne_comp : stepOne ε hε h0 hs f comm ≫ Q.d 2 1 =
    f.f 1 - P.d 1 0 ≫ stepZero ε hε h0 f comm :=
  (hs 0).liftFromProjective_comp _ _

omit h0 comm in
def stepSucc (n : ℕ) (g : P.X n ⟶ Q.X (n+1))
    (g' : P.X (n+1) ⟶ Q.X (n+2))
    (w : f.f (n+1) = P.d (n+1) n ≫ g + g' ≫ Q.d (n+2) (n+1)) :
    P.X (n+2) ⟶ Q.X (n+3) :=
  (hs (n+1)).liftFromProjective (f.f (n+2) - P.d (n+2) (n+1) ≫ g') (by simp [w])

omit h0 comm in
@[reassoc (attr := simp)]
lemma stepSucc_comp (n : ℕ) (g : P.X n ⟶ Q.X (n+1))
    (g' : P.X (n+1) ⟶ Q.X (n+2))
    (w : f.f (n+1) = P.d (n+1) n ≫ g + g' ≫ Q.d (n+2) (n+1)) :
    stepSucc hs f n g g' w ≫ Q.d (n+3) (n+2) = f.f (n+2) - P.d (n+2) (n+1) ≫ g' :=
  (hs (n+1)).liftFromProjective_comp _ _

def nullHomotopy : Homotopy f 0 :=
  Homotopy.mkInductive _ (stepZero ε hε h0 f comm) (by simp)
    (stepOne ε hε h0 hs f comm) (by simp)
    fun n ⟨g,g',w⟩ => ⟨stepSucc hs f n g g' w,by simp⟩

omit comm in
def comparison (g : P ⟶ Q) (hg : f.f 0 ≫ ε = g.f 0 ≫ ε) : Homotopy f g :=
  Homotopy.equivSubZero.invFun (nullHomotopy ε hε h0 hs (f-g) (by
    change (f.f 0 - g.f 0) ≫ ε = 0
    rw [Preadditive.sub_comp,hg,sub_self]))

end ExactTargetHomotopy

namespace StandardVertex
open CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) (v : G → H) (hv : ∀ g x, v (g*x) = φ g * v x)
variable (w : G → H) (hw : ∀ g x, w (g*x) = φ g * w x)

lemma augmentation_eq :
    map φ v hv 0 ≫ (Rep.resFunctor φ).map ((Rep.standardResolution R H).π.f 0) =
      map φ w hw 0 ≫ (Rep.resFunctor φ).map ((Rep.standardResolution R H).π.f 0) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (Rep.standardComplex.ε R H).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → G => v ∘ s)
        (MonoidAlgebra.single s 1)) =
    (Rep.standardComplex.ε R H).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → G => w ∘ s)
        (MonoidAlgebra.single s 1))
  simp [Rep.standardComplex.ε]

def homotopy : Homotopy (chainMap (R := R) φ v hv) (chainMap φ w hw) := by
  let F := Rep.resFunctor (k := R) φ
  let P := Rep.standardResolution R H
  apply ExactTargetHomotopy.comparison (F.map (P.π.f 0))
    (by
      change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
      rw [← F.map_comp,P.complex_d_comp_π_f_zero,F.map_zero])
    (P.exact₀.map F)
    (fun n => (P.exact_succ n).map F)
  exact augmentation_eq φ v hv w hw

end StandardVertex

end

end OAI
