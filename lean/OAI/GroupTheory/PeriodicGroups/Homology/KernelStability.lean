import Mathlib
import OAI.GroupTheory.PeriodicGroups.Steinberg.RankActions

namespace OAI

noncomputable section

namespace SourceBurnside.Stability
section
open Classical CategoryTheory
namespace RationalKernel
open ElementaryRanks RationalBar
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]

abbrev J (n : ℕ) := (representation (R := R) (n := n)).ker
abbrev step (n : ℕ) : Steinberg n R →* Steinberg (n+1) R :=
  Steinberg.coordinateMap Fin.castSucc (Fin.castSucc_injective n)

variable (ε : R →ₐ[ZMod 2] ZMod 2)

def kernelStep (n : ℕ) : J (R := R) n →* J (R := R) (n+1) where
  toFun j := ⟨step n j.val,by
    change representation (step n j.val)=1
    have he := DFunLike.congr_fun (next_representation ε) j.val
    change (next ε n) (representation j.val)=representation (step n j.val) at he
    rw [j.property,map_one] at he
    exact he.symm⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' j k := Subtype.ext (map_mul _ _ _)

variable {ε}
lemma central (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 6≤n) :
    J (R := R) n ≤ Subgroup.center (Steinberg n R) := by
  rw [J,rep_kernel]
  exact SteinbergAction.kernel_central ε hI hn

variable {n : ℕ} {X : Type} [Group X] (S : RationalExtension X (Group (R := R) n))

def liftKernel : J (R := R) n →* S.rightHom.ker where
  toFun j := ⟨ExtensionRootLift.hom S j.val,by
    have h := DFunLike.congr_fun (ExtensionRootLift.hom_projection S) j.val
    exact h.trans j.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' j k := Subtype.ext (map_mul _ _ _)

def character : J (R := R) n →* QGroup := S.kernelEquiv.symm.toMonoidHom.comp (liftKernel S)
lemma inl_character (j : J (R := R) n) : S.inl (character S j)=ExtensionRootLift.hom S j.val := by
  exact congrArg Subtype.val (S.kernelEquiv.apply_symm_apply (liftKernel S j))

variable (ε)

theorem restriction_surjective (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    Function.Surjective (fun ψ : J (R := R) (n+1) →* QGroup => ψ.comp (kernelStep ε n)) := by
  intro φ
  let p := representation (R := R) (n := n)
  have hc : p.ker ≤ Subgroup.center (Steinberg n R) := central hI n (by omega)
  let S := CentralPushout.extension p hc φ (representation_surjective n)
  let c := S.cocycle
  let f := next ε n
  have : IsIso (RationalHomology.map f 2) := next_h2_isIso ε hI n hn
  obtain ⟨d,b,hb⟩ := extend f c
  let D := extension d
  let M : CentralPushout.Extension p hc φ →* Extension d :=
    (morphism f c d b hb).comp S.modelEquiv.symm.toMulEquiv.toMonoidHom
  have Minl (q : QGroup) : M (S.inl q)=D.inl q := by
    change morphism f c d b hb (S.modelEquiv.symm (S.inl q))=inclusion d q
    rw [S.modelEquiv.symm.map_inl]
    exact morphism_inclusion f c d b hb q
  have Mprojection (x : CentralPushout.Extension p hc φ) : D.rightHom (M x)=f (S.rightHom x) := by
    change projection d (morphism f c d b hb (S.modelEquiv.symm x))=f (S.rightHom x)
    rw [morphism_projection]
    exact congrArg f (S.modelEquiv.symm.rightHom_map x)
  let F := M.comp (CentralPushout.canonical p hc φ)
  let L := (ExtensionRootLift.hom D).comp (step n)
  have he : F=L := by
    apply ExtensionRootLift.unique_over D
    apply MonoidHom.ext
    intro u
    change D.rightHom (M (CentralPushout.canonical p hc φ u))=D.rightHom (ExtensionRootLift.hom D (step n u))
    rw [Mprojection]
    have hx := DFunLike.congr_fun (ExtensionRootLift.hom_projection D) (step n u)
    change D.rightHom (ExtensionRootLift.hom D (step n u))=representation (step n u) at hx
    rw [hx]
    exact DFunLike.congr_fun (next_representation ε) u
  refine ⟨character D,?_⟩
  ext j
  apply D.inl_injective
  change D.inl (character D (kernelStep ε n j))=D.inl (φ j)
  rw [inl_character]
  change L j.val = _
  rw [←he]
  change M (CentralPushout.canonical p hc φ j.val)=_
  rw [CentralPushout.canonical_kernel]
  exact Minl (φ j)

end RationalKernel
end

open Classical
namespace SurjectiveDescent
variable {P G X : Type} [Group P] [Group G] [Group X]

def descend (p : P →* G) (hp : Function.Surjective p) (F : P →* X) (hk : p.ker≤F.ker) : G →* X :=
  (QuotientGroup.lift p.ker F hk).comp (QuotientGroup.quotientKerEquivOfSurjective p hp).symm.toMonoidHom

lemma descend_apply (p : P →* G) (hp : Function.Surjective p) (F : P →* X) (hk : p.ker≤F.ker) (u : P) :
    descend p hp F hk (p u)=F u := by
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  have he : e (QuotientGroup.mk' p.ker u)=p u := rfl
  change QuotientGroup.lift p.ker F hk (e.symm (p u))=F u
  rw [←he,MulEquiv.symm_apply_apply]
  rfl
end SurjectiveDescent
namespace RationalBar
variable {G H : Type} [Group G] [Group H]

lemma coboundary_of_lift (f : G →* H) (c : Cocycles H) (s : G →* Extension c)
    (hs : (projection c).comp s=f) : ∃b : C1 G →ₗ[ℚ] ℚ, (pull f c).val=b.comp (d2 G) := by
  let b : C1 G →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun g : G => -(s g).1)
  have bs (g : G) (a : ℚ) : b (Finsupp.single g a) = -a*(s g).1 := by simp [b]
  have hproj (g : G) : (s g).2=f g := DFunLike.congr_fun hs g
  refine ⟨b,?_⟩
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext
  intro a
  obtain ⟨g,h⟩ := v
  have he := congrArg Prod.fst (map_mul s g h)
  change (s (g*h)).1=(s g).1+(s h).1+value c (s g).2 (s h).2 at he
  rw [hproj,hproj] at he
  have hc : (pull f c).val (Finsupp.single (g,h) a)=a*value c (f g) (f h) := by
    rw [show Finsupp.single (g,h) a = a • Finsupp.single (g,h) 1 by simp,map_smul]
    change a*value (pull f c) g h=_
    rw [pull_value]
  change (pull f c).val (Finsupp.single (g,h) a)=b (groupHomology.d₂₁ (T G) (Finsupp.single (g,h) a))
  rw [hc,groupHomology.d₂₁_single]
  change a*value c (f g) (f h)=b (Finsupp.single h a-Finsupp.single (g*h) a+Finsupp.single g a)
  simp only [map_add,map_sub,bs]
  linear_combination -a*he

lemma coboundary_value_eq (f : G →* H) (c : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : (pull f c).val=b.comp (d2 G)) (g h : G) :
    value c (f g) (f h)=b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  have he := LinearMap.congr_fun hb (Finsupp.single (g,h) 1)
  change value (pull f c) g h=b (d2 G (Finsupp.single (g,h) 1)) at he
  rwa [pull_value,coboundary_value] at he

def liftOfCoboundary (f : G →* H) (c : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : (pull f c).val=b.comp (d2 G)) : G →* Extension c where
  toFun g := (-b (Finsupp.single g 1),f g)
  map_one' := Prod.ext (by
    change -b (Finsupp.single 1 1) = -value c 1 1
    have he := coboundary_value_eq f c b hb 1 1
    simp only [map_one,one_mul] at he
    linarith) (map_one f)
  map_mul' g h := Prod.ext (by
    change -b (Finsupp.single (g*h) 1) =
      -b (Finsupp.single g 1)+-b (Finsupp.single h 1)+value c (f g) (f h)
    linarith [coboundary_value_eq f c b hb g h]) (map_mul f g h)

lemma liftOfCoboundary_projection (f : G →* H) (c : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : (pull f c).val=b.comp (d2 G)) : (projection c).comp (liftOfCoboundary f c b hb)=f := rfl

lemma pull_id (c : Cocycles G) : pull (MonoidHom.id G) c=c := by
  apply Subtype.ext
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro a
  obtain ⟨g,h⟩ := p
  change c.val (map2 (MonoidHom.id G) (Finsupp.single (g,h) a))=c.val (Finsupp.single (g,h) a)
  simp [map2,groupHomology.chainsMap₂]

end RationalBar
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalKernel
section
open Classical CategoryTheory ElementaryRanks RationalBar
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def restriction (n : ℕ) : (J (R := R) (n+1) →* QGroup) →* (J (R := R) n →* QGroup) where
  toFun ψ := ψ.comp (kernelStep ε n)
  map_one' := by apply MonoidHom.ext; intro j; rfl
  map_mul' ψ χ := by apply MonoidHom.ext; intro j; rfl

lemma restriction_eq_one (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n)
    (ψ : J (R := R) (n+1) →* QGroup) (hψ : ψ.comp (kernelStep ε n)=1) : ψ=1 := by
  let p := representation (R := R) (n := n+1)
  have hc : p.ker ≤ Subgroup.center (Steinberg (n+1) R) := central hI (n+1) (by omega)
  let S := CentralPushout.extension p hc ψ (representation_surjective (n+1))
  let c := S.cocycle
  let F := (CentralPushout.canonical p hc ψ).comp (step n)
  have hk : (representation (R := R) (n := n)).ker ≤ F.ker := by
    intro u hu
    let j : J (R := R) n := ⟨u,hu⟩
    have he : ψ (kernelStep ε n j)=1 := DFunLike.congr_fun hψ j
    have hh := CentralPushout.canonical_kernel p hc ψ (kernelStep ε n j)
    change F u=1
    change CentralPushout.canonical p hc ψ (step n u)=1
    exact hh.trans (by rw [he,map_one])
  let s₀ := SurjectiveDescent.descend representation (representation_surjective n) F hk
  let s := S.modelEquiv.symm.toMulEquiv.toMonoidHom.comp s₀
  have hs : (projection c).comp s=next ε n := by
    apply MonoidHom.ext
    intro g
    obtain ⟨u,rfl⟩ := representation_surjective n g
    change projection c (S.modelEquiv.symm (SurjectiveDescent.descend representation
      (representation_surjective n) F hk (representation u)))=next ε n (representation u)
    rw [SurjectiveDescent.descend_apply]
    exact (S.modelEquiv.symm.rightHom_map (F u)).trans
      (DFunLike.congr_fun (next_representation ε) u).symm
  have : IsIso (RationalHomology.map (next ε n) 2) := next_h2_isIso ε hI n hn
  obtain ⟨b,hb⟩ := (pull_coboundary_iff (next ε n) c).mp (coboundary_of_lift (next ε n) c s hs)
  have hb' : (pull (MonoidHom.id _) c).val=b.comp (d2 _) := by rw [pull_id]; exact hb
  let t := liftOfCoboundary (MonoidHom.id _) c b hb'
  let L := (S.modelHom.comp t).comp p
  have he : CentralPushout.canonical p hc ψ=L := by
    apply ExtensionRootLift.unique_over S
    apply MonoidHom.ext
    intro u
    change S.rightHom (CentralPushout.canonical p hc ψ u)=S.rightHom (S.modelHom (t (p u)))
    rw [S.modelHom_projection]
    rfl
  apply MonoidHom.ext
  intro j
  apply S.inl_injective
  change S.inl (ψ j)=S.inl 1
  change CentralPushout.inclusion p hc ψ (ψ j)=CentralPushout.inclusion p hc ψ 1
  rw [←CentralPushout.canonical_kernel,he]
  change S.modelHom (t (p j.val))=CentralPushout.inclusion p hc ψ 1
  rw [j.property,map_one,map_one,map_one]

lemma restriction_injective (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    Function.Injective (restriction ε n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro ψ hψ
  change ψ=1
  exact restriction_eq_one ε hI n hn ψ hψ

def restrictionIso (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    (J (R := R) (n+1) →* QGroup) ≃* (J (R := R) n →* QGroup) :=
  MulEquiv.ofBijective (restriction ε n)
    ⟨restriction_injective ε hI n hn,restriction_surjective ε hI n hn⟩

@[simp] lemma restrictionIso_apply (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n)
    (ψ : J (R := R) (n+1) →* QGroup) : restrictionIso ε hI n hn ψ = ψ.comp (kernelStep ε n) := rfl

end

open Classical ElementaryRanks
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

abbrev cast {n q : ℕ} (h : n≤q) : Steinberg n R →* Steinberg q R :=
  Steinberg.coordinateMap (Fin.castLE h) (Fin.castLE_injective h)

omit [Algebra (ZMod 2) R] in
lemma cast_refl (n : ℕ) : cast (R := R) (le_refl n)=MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro p a
  rfl
omit [Algebra (ZMod 2) R] in
lemma cast_succ {n q : ℕ} (h : n≤q) : cast (R := R) (h.trans (Nat.le_succ q)) =
    (step q).comp (cast h) := by
  apply Steinberg.hom_ext
  intro p a
  rfl

include ε in
lemma cast_mem {n q : ℕ} (hnq : n≤q) (j : J (R := R) n) : cast hnq j.val∈J (R := R) q := by
  induction q,hnq using Nat.le_induction with
  | base => simpa only [cast_refl,MonoidHom.id_apply] using j.property
  | succ q hnq ih =>
    rw [cast_succ,MonoidHom.comp_apply]
    exact (kernelStep ε q ⟨cast hnq j.val,ih⟩).property

def kernelCast {n q : ℕ} (hnq : n≤q) : J (R := R) n →* J (R := R) q where
  toFun j := ⟨cast hnq j.val,cast_mem ε hnq j⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _left _right := Subtype.ext (map_mul _ _ _)

lemma kernelCast_refl (n : ℕ) : kernelCast ε (le_refl n)=MonoidHom.id _ := by
  apply MonoidHom.ext
  intro j
  apply Subtype.ext
  exact DFunLike.congr_fun (cast_refl (R := R) n) j.val
lemma kernelCast_succ {n q : ℕ} (hnq : n≤q) : kernelCast ε (hnq.trans (Nat.le_succ q))=
    (kernelStep ε q).comp (kernelCast ε hnq) := by
  apply MonoidHom.ext
  intro j
  apply Subtype.ext
  exact DFunLike.congr_fun (cast_succ (R := R) hnq) j.val

theorem restriction_cast_surjective (hI : MatrixNilKernel ε.toRingHom) {n q : ℕ}
    (hn : 12≤n) (hnq : n≤q) : Function.Surjective
    (fun ψ : J (R := R) q →* QGroup => ψ.comp (kernelCast ε hnq)) := by
  induction q,hnq using Nat.le_induction with
  | base =>
    intro φ
    refine ⟨φ,?_⟩
    dsimp only
    rw [kernelCast_refl,MonoidHom.comp_id]
  | succ q hnq ih =>
    intro φ
    obtain ⟨ψ,hψ⟩ := ih φ
    obtain ⟨χ,hχ⟩ := (restrictionIso ε hI q (hn.trans hnq)).surjective ψ
    change χ.comp (kernelStep ε q)=ψ at hχ
    refine ⟨χ,?_⟩
    dsimp only at hψ hχ ⊢
    rw [kernelCast_succ,←MonoidHom.comp_assoc,hχ]
    exact hψ

end SourceBurnside.Stability.RationalKernel

namespace SourceBurnside.Stability.RationalDetection
open Classical
variable {A : Type} [CommGroup A]

lemma character_nonzero_of_not_finite (a : A) (ha : ¬IsOfFinOrder a) :
    ∃φ : A →* QGroup, φ a=Multiplicative.ofAdd (1 : ℚ) := by
  let f : ℤ →ₗ[ℤ] Additive A := LinearMap.toSpanSingleton ℤ _ (Additive.ofMul a)
  have hf : Function.Injective f := by
    intro i j h
    apply (injective_zpow_iff_not_isOfFinOrder.mpr ha)
    exact congrArg Additive.toMul h
  let g : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
  obtain ⟨h,hh⟩ := (Module.Baer.of_divisible ℚ).extension_property f hf g
  let φ : A →* QGroup :=
    { toFun := fun x => Multiplicative.ofAdd (h (Additive.ofMul x))
      map_one' := by change h 0=0; exact map_zero h
      map_mul' := fun x y => by
        change h (Additive.ofMul x+Additive.ofMul y)=h (Additive.ofMul x)+h (Additive.ofMul y)
        exact map_add h _ _ }
  refine ⟨φ,?_⟩
  have he := LinearMap.congr_fun hh 1
  change h (f 1)=g 1 at he
  have hg : g 1=1 := by simp [g]
  rw [hg] at he
  change h (Additive.ofMul a)=(1 : ℚ)
  simpa only [f,LinearMap.toSpanSingleton_apply,one_smul] using he

lemma finite_of_characters_vanish (a : A) (ha : ∀φ : A →* QGroup,φ a=1) : IsOfFinOrder a := by
  by_contra hn
  obtain ⟨φ,hφ⟩ := character_nonzero_of_not_finite a hn
  have he := ha φ
  rw [hφ] at he
  have : (1 : ℚ)=0 := congrArg Multiplicative.toAdd he
  exact one_ne_zero this

lemma character_finite_eq_one {B : Type} [Group B] (φ : B →* QGroup) {a : B} (ha : IsOfFinOrder a) : φ a=1 := by
  obtain ⟨m,hm,he⟩ := ha.exists_pow_eq_one
  have hφ : (φ a)^m=1 := by rw [←map_pow,he,map_one]
  have hx : (m : ℚ)*(φ a).toAdd=0 := by
    simpa only [toAdd_pow,toAdd_one,nsmul_eq_mul] using congrArg Multiplicative.toAdd hφ
  have hm' : (m : ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  change (φ a).toAdd=0
  exact (mul_eq_zero.mp hx).resolve_left hm'

end SourceBurnside.Stability.RationalDetection

end

end OAI
