import Mathlib
import OAI.GroupTheory.FiniteType.SteinbergFinitePresentation

namespace OAI

noncomputable section
open scoped Pointwise
namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f) (a : U)

def innerTwist : U →* U := (MulAut.conj a).toMonoidHom.comp f

@[simp] lemma innerTwist_apply (u : U) : innerTwist f a u = a * f u * a⁻¹ := rfl

include hf in
lemma innerTwist_injective : Function.Injective (innerTwist f a) :=
  (MulAut.conj a).injective.comp hf

lemma changed_stable_relation (u : U) :
    embed f hf u * (stable f hf * (embed f hf a)⁻¹) =
      (stable f hf * (embed f hf a)⁻¹) * embed f hf (innerTwist f a u) := by
  simp only [innerTwist_apply,map_mul,map_inv]
  rw [← mul_assoc,embed_mul_stable]
  group

def changeStableHom : Torus (innerTwist f a) (innerTwist_injective f hf a) →* Torus f hf :=
  evaluation (innerTwist f a) (innerTwist_injective f hf a)
    (embed f hf) (stable f hf * (embed f hf a)⁻¹) (changed_stable_relation f hf a)

lemma restored_stable_relation (u : U) :
    embed (innerTwist f a) (innerTwist_injective f hf a) u *
      (stable (innerTwist f a) (innerTwist_injective f hf a) *
        embed (innerTwist f a) (innerTwist_injective f hf a) a) =
    (stable (innerTwist f a) (innerTwist_injective f hf a) *
        embed (innerTwist f a) (innerTwist_injective f hf a) a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) (f u) := by
  rw [← mul_assoc,embed_mul_stable]
  simp only [innerTwist_apply,map_mul,map_inv]
  group

def restoreStableHom : Torus f hf →* Torus (innerTwist f a) (innerTwist_injective f hf a) :=
  evaluation f hf (embed (innerTwist f a) (innerTwist_injective f hf a))
    (stable (innerTwist f a) (innerTwist_injective f hf a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) a)
    (restored_stable_relation f hf a)

@[simp] lemma changeStableHom_embed (u : U) :
    changeStableHom f hf a (embed (innerTwist f a) (innerTwist_injective f hf a) u) =
    embed f hf u := evaluation_embed _ _ _ _ _ _

@[simp] lemma changeStableHom_stable :
    changeStableHom f hf a (stable (innerTwist f a) (innerTwist_injective f hf a)) =
    stable f hf * (embed f hf a)⁻¹ := evaluation_stable _ _ _ _ _

@[simp] lemma restoreStableHom_embed (u : U) :
    restoreStableHom f hf a (embed f hf u) =
    embed (innerTwist f a) (innerTwist_injective f hf a) u := evaluation_embed _ _ _ _ _ _

@[simp] lemma restoreStableHom_stable :
    restoreStableHom f hf a (stable f hf) =
    stable (innerTwist f a) (innerTwist_injective f hf a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) a := evaluation_stable _ _ _ _ _

lemma change_restore : (changeStableHom f hf a).comp (restoreStableHom f hf a) = MonoidHom.id _ := by
  apply hom_ext
  · intro u
    simp
  · simp

lemma restore_change : (restoreStableHom f hf a).comp (changeStableHom f hf a) = MonoidHom.id _ := by
  apply hom_ext
  · intro u
    simp
  · simp

def changeStableEquiv : Torus (innerTwist f a) (innerTwist_injective f hf a) ≃* Torus f hf where
  toFun := changeStableHom f hf a
  invFun := restoreStableHom f hf a
  left_inv g := DFunLike.congr_fun (restore_change f hf a) g
  right_inv g := DFunLike.congr_fun (change_restore f hf a) g
  map_mul' := (changeStableHom f hf a).map_mul

end AscendingHNN

namespace HomStabilizer
variable {G H X : Type*} [Group G] [Group H]

def fixedTuple (ρ : G →* Equiv.Perm X) {J : Type*} (v : J → X) : Subgroup G where
  carrier := {g | ∀ j, ρ g (v j) = v j}
  one_mem' := by intro j; simp
  mul_mem' := by intro g h hg hh j; simp only [map_mul,Equiv.Perm.mul_apply]; rw [hh j,hg j]
  inv_mem' := by
    intro g hg j
    have h := congrArg (ρ g).symm (hg j)
    simpa only [map_inv,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using h.symm

@[simp] lemma mem_fixedTuple (ρ : G →* Equiv.Perm X) {J : Type*} (v : J → X) (g : G) :
    g ∈ fixedTuple ρ v ↔ ∀ j, ρ g (v j)=v j := Iff.rfl

def preimageEquiv (e : G ≃* H) (K : Subgroup H) : K.comap e.toMonoidHom ≃* K where
  toFun g := ⟨e g,g.property⟩
  invFun h := ⟨e.symm h,by change e (e.symm h.val) ∈ K; simpa only [e.apply_symm_apply] using h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

end HomStabilizer

namespace TorusStabilizer
open SequentialLimit SequentialAction AscendingHNN TorusAction HomStabilizer
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x)=f g • s x)
variable {J : Type*} (z : J → X) (a : U) (ha : ∀ j, a • s (z j)=z j)

def stageSubgroup : Subgroup U := fixedTuple (MulAction.toPermHom U X) z

def limitSubgroup : Subgroup (Torus f hf) :=
  fixedTuple (representation f hf s heq) (fun j => of s 0 (z j))

def changedSubgroup : Subgroup (Torus (innerTwist f a) (innerTwist_injective f hf a)) :=
  (limitSubgroup f hf s heq z).comap (changeStableHom f hf a)

include ha in
lemma changed_stable_mem :
    stable (innerTwist f a) (innerTwist_injective f hf a) ∈ changedSubgroup f hf s heq z a := by
  change ∀ j, representation f hf s heq
    (changeStableHom f hf a (stable (innerTwist f a) (innerTwist_injective f hf a)))
    (of s 0 (z j)) = of s 0 (z j)
  intro j
  rw [changeStableHom_stable,map_mul,map_inv,representation_stable,representation_embed]
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply,basePerm_of,Function.iterate_zero,id_eq,shift_of]
  have hz : a⁻¹ • z j = s (z j) := by
    calc a⁻¹ • z j = a⁻¹ • (a • s (z j)) := congrArg (fun x => a⁻¹ • x) (ha j).symm
         _ = s (z j) := inv_smul_smul a (s (z j))
  rw [hz,of_succ]

lemma base_mem_iff (hs : Function.Injective s) (u : U) :
    u ∈ HNNSubgroup.base (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) ↔ u ∈ stageSubgroup z := by
  change (∀ j, representation f hf s heq
    (changeStableHom f hf a (embed (innerTwist f a) (innerTwist_injective f hf a) u))
      (of s 0 (z j))=of s 0 (z j)) ↔ ∀ j, u • z j=z j
  simp only [changeStableHom_embed,representation_embed,basePerm_of,Function.iterate_zero,id_eq]
  exact forall_congr' (fun _ => (of_injective s hs 0).eq_iff)

include ha in

def torusEquiv :
    Torus (HNNSubgroup.baseMap (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha))
      (HNNSubgroup.baseMap_injective (innerTwist f a) (innerTwist_injective f hf a)
        (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha)) ≃*
    limitSubgroup f hf s heq z :=
  (HNNSubgroup.equiv (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha)).trans
    (preimageEquiv (changeStableEquiv f hf a) (limitSubgroup f hf s heq z))

end TorusStabilizer

namespace StageGeometry
open StageConstruction

structure PairDiagrams {Q W X Y : Type} [Group Q] [Group W]
    [MulAction Q X] [MulAction W Y] (K : Type) [CommRing K]
    (ι : Q →* W) (point : X → Y) where
  map : BinaryPrefixOperators.idempotents K → (Q →* W)
  identity : map ⟨1,BinaryPrefixOperators.identity_mem K⟩ = ι
  commute : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ _hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 → ∀ u v, Commute (map E u) (map P v)
  addition : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    ∀ u, map ⟨E.val+P.val,hSum⟩ u = map E u * map P u
  fixed : ∀ E q x, q • x = x → map E q • point x = point x

variable {R Y W : Type} [Ring R] [Group W] [MulAction W Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (S : Y → R) (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι)

abbrev trans := delta φ D ρ ι
abbrev transInjective := delta_injective φ D ρ ι hφ hρ hι
abbrev shift := sigma φ S point
include hρS hpoint in
lemma compatible (q : Q R) (x : X R) :
    shift φ S point (q • x) = trans φ D ρ ι q • shift φ S point x :=
  (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm

variable {J : Type} (z : J → X R) (a : Q R)
variable (ha : ∀ j, a • shift φ S point (z j) = z j)

abbrev changed := TorusStabilizer.changedSubgroup
  (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι)
  (shift φ S point) (compatible φ D S ρ ι point hρS hpoint) z a
abbrev base := HNNSubgroup.base
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
abbrev endomorphism := HNNSubgroup.baseMap
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
  (TorusStabilizer.changed_stable_mem _ _ _ _ z a ha)
abbrev endomorphism_injective := HNNSubgroup.baseMap_injective
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
  (TorusStabilizer.changed_stable_mem _ _ _ _ z a ha)

variable (hs : Function.Injective (shift φ S point))
include hs in
lemma base_iff (q : Q R) :
    q ∈ base φ D S ρ ι point hρS hpoint hφ hρ hι z a ↔ ∀ j, q • z j = z j :=
  TorusStabilizer.base_mem_iff _ _ _ _ z a hs q

include ha in
lemma compressed_tuple (j : J) :
    action a (Pi.single first (φ (φ (S (point (z j)))))) = z j := ha j

def baseEquiv : base φ D S ρ ι point hρS hpoint hφ hρ hι z a ≃*
    compressedFixing φ (fun j => S (point (z j))) a where
  toFun q := ⟨q.val, by
    intro j
    change q.val • (a • shift φ S point (z j)) = a • shift φ S point (z j)
    rw [ha j]
    exact (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs q.val).mp q.property j⟩
  invFun q := ⟨q.val, (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs q.val).mpr (by
    intro j
    have h := q.property j
    change q.val • (a • shift φ S point (z j)) = a • shift φ S point (z j) at h
    rwa [ha j] at h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev compressedUnits : compressedFixing φ (fun j => S (point (z j))) a →* Rˣ :=
  (ρ.comp ι).comp (compressedFixing φ (fun j => S (point (z j))) a).subtype

include ha in
lemma compressed_fixed (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    (q : Q R) • z j = z j := by
  have h := q.property j
  change (q : Q R) • (a • shift φ S point (z j)) = a • shift φ S point (z j) at h
  rwa [ha j] at h

include hpoint ha in
lemma compressed_point_fixed (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    ι q • point (z j) = point (z j) := by
  rw [hpoint,compressed_fixed φ S point z a ha q j]

include hρS hpoint ha in
lemma units_prefix (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    (compressedUnits φ S ρ ι point z a q).val*S (point (z j))=S (point (z j)) := by
  change (ρ (ι q)).val * S (point (z j)) = _
  rw [hρS,compressed_point_fixed φ S ι point hpoint z a ha q j]

variable (T : Y → R) (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
include hTρ hpoint ha in
lemma units_suffix (q : compressedFixing φ (fun j => S (point (z j))) a) (j : J) :
    T (point (z j))*(compressedUnits φ S ρ ι point z a q).val=T (point (z j)) := by
  change T (point (z j)) * (ρ (ι q)).val = _
  rw [hTρ]
  congr 1
  apply inv_smul_eq_iff.mpr
  exact (compressed_point_fixed φ S ι point hpoint z a ha q j).symm

variable (K : Type) [CommRing K] (F : PairDiagrams K ι point)

abbrev conjugated : W →* Q R :=
  (MulAut.conj a).toMonoidHom.comp ((transitionUnits φ D).comp ρ)

include hρS ha hs in
lemma conjugated_mem (E : BinaryPrefixOperators.idempotents K)
    (u : base φ D S ρ ι point hρS hpoint hφ hρ hι z a) :
    conjugated φ D ρ a (F.map E u.val) ∈
      base φ D S ρ ι point hρS hpoint hφ hρ hι z a := by
  apply (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs _).mpr
  intro j
  have hu := (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs _).mp u.property j
  have hfix := F.fixed E u.val (z j) hu
  have hz' : a⁻¹ • z j = shift φ S point (z j) := by
    calc
      a⁻¹ • z j = a⁻¹ • (a • shift φ S point (z j)) :=
        congrArg (fun x => a⁻¹ • x) (ha j).symm
      _ = shift φ S point (z j) := inv_smul_smul a _
  change (a * transitionUnits φ D (ρ (F.map E u.val)) * a⁻¹) • z j = z j
  change action (a * transitionUnits φ D (ρ (F.map E u.val)) * a⁻¹) (z j) = z j
  rw [map_mul,map_mul]
  change a • (transitionUnits φ D (ρ (F.map E u.val)) • (a⁻¹ • z j)) = z j
  rw [hz']
  change a • action (transitionUnits φ D (ρ (F.map E u.val)))
    (beta φ S (point (z j))) = z j
  rw [transitionUnits_beta φ D S _ _ (point (z j)) (by rw [hρS,hfix])]
  exact ha j

def diagramMap (E : BinaryPrefixOperators.idempotents K) :
    base φ D S ρ ι point hρS hpoint hφ hρ hι z a →*
      base φ D S ρ ι point hρS hpoint hφ hρ hι z a :=
  ((conjugated φ D ρ a).comp ((F.map E).comp
    (base φ D S ρ ι point hρS hpoint hφ hρ hι z a).subtype)).codRestrict _
    (conjugated_mem φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs K F E)

def splittings : ListChains.IdempotentSplittings
    (base φ D S ρ ι point hρS hpoint hφ hρ hι z a) K
    (endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha) where
  map := diagramMap φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs K F
  identity := by
    apply MonoidHom.ext
    intro u
    apply Subtype.ext
    change conjugated φ D ρ a (F.map ⟨1,_⟩ u.val) = _
    rw [F.identity]
    rfl
  commute E P hSum hEP hPE u v := by
    apply Subtype.ext
    exact ((F.commute E P hSum hEP hPE u.val v.val).map
      (conjugated φ D ρ a)).eq
  addition E P hSum hEP hPE u := by
    apply Subtype.ext
    change conjugated φ D ρ a (F.map ⟨_,hSum⟩ u.val) = _
    rw [F.addition E P hSum hEP hPE,map_mul]
    rfl

variable [Fintype J] [DecidableEq J] [DecidableEq Y]
variable (e : R) (hTS : ∀ y y', T y*S y'=if y=y' then e else 0)
variable (hSe : ∀ y, S y*e=S y) (hz : Function.Injective z)
variable (hpt : Function.Injective point)

include ha hs hρS hpoint hTρ hTS hSe hz hpt in

theorem factor :
    ∃ (α : base φ D S ρ ι point hρS hpoint hφ hρ hι z a →*
        Steinberg.Group (Fin 6) R)
      (b : Steinberg.Group (Fin 6) R →*
        base φ D S ρ ι point hρS hpoint hφ hρ hι z a),
      b.comp α = endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha := by
  let E := baseEquiv φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs
  obtain ⟨α,b,hb⟩ := stabilizer_factor φ D a e S T hTS hSe (point ∘ z)
    (hpt.comp hz) (compressedUnits φ S ρ ι point z a)
    (units_prefix φ S ρ ι point hρS hpoint z a ha)
    (units_suffix φ S ρ ι point hpoint z a ha T hTρ)
  refine ⟨α.comp E.toMonoidHom,E.symm.toMonoidHom.comp b,?_⟩
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  have h := congrArg (fun f => f (E u)) hb
  exact congrArg (fun q : compressedFixing φ (fun j => S (point (z j))) a => q.val) h

variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include ha hs hρS hpoint hTρ hTS hSe hz hpt F₂ F₃ in

theorem aligned_geometric [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TorusStabilizer.limitSubgroup (trans φ D ρ ι)
        (transInjective φ D ρ ι hφ hρ hι) (shift φ S point)
        (compatible φ D S ρ ι point hρS hpoint) z) := by
  obtain ⟨α,b,hb⟩ := factor φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs T hTρ
    e hTS hSe hz hpt
  have hgeo := SimpleFInftyOvergroups.ascending_torus_geometric
    (endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha)
    (endomorphism_injective φ D S ρ ι point hρS hpoint hφ hρ hι z a ha)
    α b hb.symm
    (splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 2) F₂)
    (splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 3) F₃)
  apply SimpleFInftyOvergroups.HasTypeFInfty.of_equiv _ hgeo
  exact (AscendingHNN.presentationEquiv _ _).symm.trans
    (TorusStabilizer.torusEquiv (trans φ D ρ ι)
      (transInjective φ D ρ ι hφ hρ hι) (shift φ S point)
      (compatible φ D S ρ ι point hρS hpoint) z a ha)

include ha hs hρS hpoint hTρ hTS hSe hz hpt F₂ F₃ in

theorem aligned_geometric_of_ring_presentation
    (A : Type) [Finite A] (π : SteinbergFinitePresentation.Coeff A →ₙ+* R)
    (hπ : Function.Surjective π) (rel : Set (SteinbergFinitePresentation.Coeff A))
    (hrel : rel.Finite)
    (hker : {r | π r=0}=(TwoSidedIdeal.span rel : Set (SteinbergFinitePresentation.Coeff A))) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TorusStabilizer.limitSubgroup (trans φ D ρ ι)
        (transInjective φ D ρ ι hφ hρ hι) (shift φ S point)
        (compatible φ D S ρ ι point hρS hpoint) z) := by
  let := SteinbergFinitePresentation.rank_six_finitelyPresented A π hπ rel hrel hker
  exact aligned_geometric φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs T hTρ
    e hTS hSe hz hpt F₂ F₃

end StageGeometry

end

end OAI
