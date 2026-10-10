import Mathlib
import OAI.GroupTheory.PeriodicGroups.Homology.FiniteNormalHomology

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.ElementaryRanks
open Classical CategoryTheory MatrixGenerators MatrixK1
variable {R : Type} [Ring R]

abbrev Group (n : ℕ) := E (R := R) (ι := Fin n)

def representation {n : ℕ} : Steinberg n R →* Group (R := R) n :=
  Elementary.representation.codRestrict _ (fun u => by
    change Elementary.representation u ∈ E
    rw [←representation_range (R := R) n]
    exact ⟨u,rfl⟩)

@[simp] lemma representation_val {n : ℕ} (u : Steinberg n R) :
    (representation u).val = Elementary.representation u := rfl

lemma representation_surjective (n : ℕ) : Function.Surjective (representation (R := R) (n := n)) := by
  rintro ⟨g,hg⟩
  change g∈E at hg
  rw [←representation_range (R := R) n] at hg
  obtain ⟨u,rfl⟩ := hg
  exact ⟨u,rfl⟩

def root {n : ℕ} (p : Root n) (a : R) : Group (R := R) n := representation (Steinberg.x p a)
@[simp] lemma root_val {n : ℕ} (p : Root n) (a : R) :
    (root p a).val=elementary p.row p.col p.ne a := by
  simp only [root,representation_val,Elementary.representation_x,SteinbergAction.elementary_eq_e]

lemma rep_kernel {n : ℕ} : (representation (R := R) (n := n)).ker = Elementary.representation.ker := by
  ext u
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

variable [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)

def next (n : ℕ) : Group (R := R) n →* Group (R := R) (n+1) :=
  letI : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  (ColumnRelabel.elementaryEquiv (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1))).toMonoidHom.comp
    (SingletonFrameEdge.blockHom ε)

lemma next_root {n : ℕ} (p : Root n) (a : R) : next ε n (root p a) =
    root ⟨Fin.castSucc p.row,Fin.castSucc p.col,(Fin.castSucc_injective n).ne p.ne⟩ a := by
  let : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  apply Subtype.ext
  change relabel finSumFinEquiv (SingletonFrameEdge.blockHom ε (root p a)).val = _
  rw [SingletonFrameEdge.blockHom_val,root_val,blockInclusion_elementary,relabel_elementary,root_val]
  congr 1

lemma next_representation {n : ℕ} : (next ε n).comp representation =
    (representation (R := R)).comp (Steinberg.coordinateMap Fin.castSucc (Fin.castSucc_injective n)) := by
  apply Steinberg.hom_ext
  intro p a
  simpa only [MonoidHom.comp_apply,Steinberg.coordinateMap_x,root,Root.map] using next_root ε p a

lemma next_h2_isIso (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    IsIso (RationalHomology.map (next ε n) 2) := by
  let : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  have := SingletonFrameEdge.block_h2_isIso (ι := Fin n) ε hI (by simpa using hn)
  have := RationalHomology.equiv_isIso (ColumnRelabel.elementaryEquiv
    (R := R) (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1))) 2
  rw [next,RationalHomology.map_comp]
  infer_instance

end SourceBurnside.Stability.ElementaryRanks

namespace SourceBurnside.Stability
section
open Classical
namespace FiniteRootPairs
variable {G : Type*} [Group G]

lemma finite_pair (a b : G) (ha : a^2=1) (hb : b^2=1) (hab : IsOfFinOrder (a*b)) :
    Finite (Subgroup.closure ({a,b} : Set G)) := by
  let C := Subgroup.zpowers (a*b)
  let D : Set G := (C : Set G) ∪ ((a * ·) '' (C : Set G))
  have ha' : a*a=1 := by simpa only [pow_two] using ha
  have hb' : b*b=1 := by simpa only [pow_two] using hb
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_left ha'
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_left hb'
  have hba : b*a=(a*b)⁻¹ := by simp only [mul_inv_rev,hai,hbi]
  have finiteC : (C : Set G).Finite := Set.finite_coe_iff.mp hab.finite_zpowers
  have hD : D.Finite := finiteC.union (finiteC.image (a * ·))
  have hg (x : G) (hx : x∈({a,b}:Set G)) (y : G) (hy : y∈D) : x*y∈D := by
    rcases hx with hx | hx
    · have hxa : x=a := hx
      subst x
      rcases hy with hy | ⟨k,hk,rfl⟩
      · exact Or.inr ⟨y,hy,rfl⟩
      · exact Or.inl (by simpa only [←mul_assoc,ha',one_mul] using hk)
    · have hxb : x=b := hx
      subst x
      rcases hy with hy | ⟨k,hk,rfl⟩
      · refine Or.inr ⟨(a*b)*y,C.mul_mem (Subgroup.mem_zpowers (a*b)) hy,?_⟩
        simp only [←mul_assoc,ha',one_mul]
      · exact Or.inl (by
          rw [←mul_assoc,hba]
          exact C.mul_mem (C.inv_mem (Subgroup.mem_zpowers (a*b))) hk)
  have hcl : (Subgroup.closure ({a,b}:Set G) : Set G) ⊆ D := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact Or.inl C.one_mem
    | mul_left z hz y hy ih => exact hg z hz y ih
    | inv_mul_cancel z hz y hy ih =>
      have hz' : z⁻¹=z := by rcases hz with rfl | ⟨rfl⟩; exact hai; exact hbi
      rw [hz']
      exact hg z hz y ih
  exact (hD.subset hcl).to_subtype

lemma finite_pair_commute (a b : G) (ha : a^2=1) (hb : b^2=1) (hc : Commute a b) :
    Finite (Subgroup.closure ({a,b}:Set G)) :=
  finite_pair a b ha hb (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [hc.mul_pow,ha,hb,one_mul]⟩)

end FiniteRootPairs
end

open Classical
namespace RationalExtension
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

def finiteOrderLift (g : G) (hg : IsOfFinOrder g) : X :=
  letI : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  S.liftFinite (Subgroup.zpowers g) ⟨g,Subgroup.mem_zpowers g⟩

lemma finiteOrderLift_projection (g : G) (hg : IsOfFinOrder g) : S.rightHom (S.finiteOrderLift g hg)=g := by
  let : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  exact S.rightHom_liftFinite (Subgroup.zpowers g) _
lemma finiteOrderLift_torsion (g : G) (hg : IsOfFinOrder g) : IsOfFinOrder (S.finiteOrderLift g hg) := by
  let : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  exact S.liftFinite_finite_order (Subgroup.zpowers g) _
end RationalExtension
namespace ExtensionRootLift
open ElementaryRanks
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable {n : ℕ}

lemma add_self_zero (a : R) : a+a=0 := by
  have ht : (2 : ZMod 2)=0 := by decide
  calc
    a+a=(2 : ZMod 2) • a := (two_smul (ZMod 2) a).symm
    _=0 := by rw [ht,zero_smul]

lemma x_sq (p : Root n) (a : R) : (Steinberg.x p a)^2=1 := by
  rw [pow_two,←Steinberg.x_add,add_self_zero,Steinberg.x_zero]
lemma root_sq (p : Root n) (a : R) : (root p a)^2=1 := by
  rw [root,←map_pow,x_sq,map_one]
lemma root_torsion (p : Root n) (a : R) : IsOfFinOrder (root p a) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,root_sq p a⟩
omit [Algebra (ZMod 2) R] in
lemma root_add (p : Root n) (a b : R) : root p (a+b)=root p a*root p b := by
  simp only [root,Steinberg.x_add,map_mul]
omit [Algebra (ZMod 2) R] in
lemma root_commute (p q : Root n) (h1 : p.col≠q.row) (h2 : p.row≠q.col) (a b : R) :
    Commute (root p a) (root q b) := (Steinberg.x_commute p q h1 h2 a b).map representation
omit [Algebra (ZMod 2) R] in
lemma root_same_commute (p : Root n) (a b : R) : Commute (root p a) (root p b) := by
  show root p a*root p b=root p b*root p a
  rw [←root_add,←root_add,add_comm]
omit [Algebra (ZMod 2) R] in
lemma root_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    bracket (root ⟨i,j,hij⟩ a) (root ⟨j,k,hjk⟩ b) = root ⟨i,k,hik⟩ (a*b) := by
  simpa only [root,map_bracket] using congrArg representation (Steinberg.x_mul i j k hij hjk hik a b)

lemma consecutive_finite (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    Finite (Subgroup.closure ({root ⟨i,j,hij⟩ a,root ⟨j,k,hjk⟩ b} : Set (Group (R := R) n))) := by
  apply FiniteRootPairs.finite_pair _ _ (root_sq _ _) (root_sq _ _)
  have hi : (root ⟨i,j,hij⟩ a)⁻¹=root ⟨i,j,hij⟩ a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using root_sq ⟨i,j,hij⟩ a)
  have hj : (root ⟨j,k,hjk⟩ b)⁻¹=root ⟨j,k,hjk⟩ b :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using root_sq ⟨j,k,hjk⟩ b)
  have he : (root ⟨i,j,hij⟩ a*root ⟨j,k,hjk⟩ b)^2=root ⟨i,k,hik⟩ (a*b) := by
    simpa only [bracket,hi,hj,pow_two,mul_assoc] using root_mul i j k hij hjk hik a b
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨4,by decide,?_⟩
  rw [show 4=2*2 by decide,pow_mul,he,root_sq]

lemma unique_over {X G : Type} [Group X] [Group G] (S : RationalExtension X G)
    (f g : Steinberg n R →* X) (h : S.rightHom.comp f=S.rightHom.comp g) : f=g := by
  apply Steinberg.hom_ext
  intro p a
  apply S.torsion_lift_unique
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [←map_pow,x_sq,map_one]⟩
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [←map_pow,x_sq,map_one]⟩
  · exact DFunLike.congr_fun h (Steinberg.x p a)

variable {X : Type} [Group X] (S : RationalExtension X (Group (R := R) n))

def lift (p : Root n) (a : R) : X := S.finiteOrderLift (root p a) (root_torsion p a)
lemma projection_lift (p : Root n) (a : R) : S.rightHom (lift S p a)=root p a :=
  S.finiteOrderLift_projection _ _
lemma lift_torsion (p : Root n) (a : R) : IsOfFinOrder (lift S p a) :=
  S.finiteOrderLift_torsion _ _
lemma lift_eq_finite (H : Subgroup (Group (R := R) n)) [Finite H] (p : Root n) (a : R)
    (h : root p a∈H) : lift S p a=S.liftFinite H ⟨root p a,h⟩ :=
  S.torsion_lift_unique (lift_torsion S p a) (S.liftFinite_finite_order H _)
    ((projection_lift S p a).trans (S.rightHom_liftFinite H ⟨root p a,h⟩).symm)

lemma lift_add (p : Root n) (a b : R) : lift S p (a+b)=lift S p a*lift S p b := by
  let H := Subgroup.closure ({root p a,root p b} : Set (Group (R := R) n))
  let : Finite H := FiniteRootPairs.finite_pair_commute _ _ (root_sq _ _) (root_sq _ _) (root_same_commute p a b)
  have ha : root p a∈H := Subgroup.subset_closure (by simp)
  have hb : root p b∈H := Subgroup.subset_closure (by simp)
  have hab : root p (a+b)∈H := root_add p a b ▸ H.mul_mem ha hb
  rw [lift_eq_finite S H p a ha,lift_eq_finite S H p b hb,lift_eq_finite S H p (a+b) hab,←map_mul]
  congr 1
  exact Subtype.ext (root_add p a b)

lemma lift_commute (p q : Root n) (h1 : p.col≠q.row) (h2 : p.row≠q.col) (a b : R) :
    Commute (lift S p a) (lift S q b) := by
  let H := Subgroup.closure ({root p a,root q b} : Set (Group (R := R) n))
  let : Finite H := FiniteRootPairs.finite_pair_commute _ _ (root_sq _ _) (root_sq _ _) (root_commute p q h1 h2 a b)
  have ha : root p a∈H := Subgroup.subset_closure (by simp)
  have hb : root q b∈H := Subgroup.subset_closure (by simp)
  rw [lift_eq_finite S H p a ha,lift_eq_finite S H q b hb]
  apply Commute.map
  exact Subtype.ext (root_commute p q h1 h2 a b).eq

lemma lift_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    bracket (lift S ⟨i,j,hij⟩ a) (lift S ⟨j,k,hjk⟩ b) = lift S ⟨i,k,hik⟩ (a*b) := by
  let H := Subgroup.closure ({root ⟨i,j,hij⟩ a,root ⟨j,k,hjk⟩ b} : Set (Group (R := R) n))
  let : Finite H := consecutive_finite i j k hij hjk hik a b
  have ha : root ⟨i,j,hij⟩ a∈H := Subgroup.subset_closure (by simp)
  have hb : root ⟨j,k,hjk⟩ b∈H := Subgroup.subset_closure (by simp)
  let A : H := ⟨root ⟨i,j,hij⟩ a,ha⟩
  let B : H := ⟨root ⟨j,k,hjk⟩ b,hb⟩
  have he : S.liftFinite H (bracket A B)=lift S ⟨i,k,hik⟩ (a*b) :=
    S.torsion_lift_unique (S.liftFinite_finite_order H _) (lift_torsion S _ _)
      (by rw [S.rightHom_liftFinite,projection_lift]; exact root_mul i j k hij hjk hik a b)
  rw [←he,map_bracket,lift_eq_finite S H _ a ha,lift_eq_finite S H _ b hb]

def hom : Steinberg n R →* X := Steinberg.lift (lift S) (lift_add S) (lift_commute S) (lift_mul S)
@[simp] lemma hom_x (p : Root n) (a : R) : hom S (Steinberg.x p a)=lift S p a := Steinberg.lift_x ..
lemma hom_projection : S.rightHom.comp (hom S)=representation := by
  apply Steinberg.hom_ext
  intro p a
  change S.rightHom (hom S (Steinberg.x p a))=root p a
  rw [hom_x,projection_lift]

lemma hom_unique (f : Steinberg n R →* X) (hf : S.rightHom.comp f=representation) : f=hom S := by
  apply Steinberg.hom_ext
  intro p a
  apply S.torsion_lift_unique
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [←map_pow,x_sq,map_one]⟩
  · rw [hom_x]; exact lift_torsion S p a
  · change (S.rightHom.comp f) (Steinberg.x p a)=_
    rw [hf,hom_x,projection_lift]
    rfl

end ExtensionRootLift
end SourceBurnside.Stability

namespace SourceBurnside.Stability.SteinbergAction
section
open Classical Steinberg MatrixGenerators Kernel

def preservers {G : Type*} [Group G] (S : Subgroup G) : Subgroup (MulAut G) where
  carrier := {f | ∀g, f g∈S ↔ g∈S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' {f h} hf hh g := (hf (h g)).trans (hh g)
  inv_mem' {f} hf g := by
    have hh := hf (f⁻¹ g)
    simpa using hh.symm

variable {n : ℕ} {R : Type*} [Ring R]

lemma scale_strip (u : Fin n → Rˣ) (H L : Finset (Fin n)) (hd : Disjoint H L)
    {g : Steinberg n R} (hg : g∈Strip H L hd) : scale u g∈Strip H L hd := by
  have hh : Strip H L hd ≤ (Strip H L hd).comap (scale u).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨p,a,rfl⟩
    change scale u (x (rectPosition H L hd p) a) ∈ Strip H L hd
    rw [scale_x]
    exact Subgroup.subset_closure ⟨p,_,rfl⟩
  exact hh hg

lemma scale_preserves_strip (u : Fin n → Rˣ) (H L : Finset (Fin n)) (hd : Disjoint H L) :
    scale u∈preservers (Strip H L hd) := by
  intro g
  constructor
  · intro hg
    have hh := scale_strip (fun i => (u i)⁻¹) H L hd hg
    rw [←scale_inv] at hh
    change (scale u).symm (scale u g)∈Strip H L hd at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
  · exact scale_strip u H L hd

lemma conj_preserves_column (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t) (a : R) :
    MulAut.conj (x p a)∈preservers (columnStrip t) := by
  have hh := away_le_column_normalizer (R := R) t
    (Subgroup.subset_closure ⟨p,a,hpt,hct,rfl⟩)
  intro g
  exact (Subgroup.mem_normalizer_iff.mp hh g).symm

lemma conj_preserves_row (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t) (a : R) :
    MulAut.conj (x p a)∈preservers (rowStrip t) := by
  have hh := away_le_row_normalizer (R := R) t
    (Subgroup.subset_closure ⟨p,a,hpt,hct,rfl⟩)
  intro g
  exact (Subgroup.mem_normalizer_iff.mp hh g).symm

lemma fixes_strip (f : MulAut (Steinberg n R))
    (hf : ∀g, Elementary.representation (f g) = Elementary.representation g)
    (H L : Finset (Fin n)) (hd : Disjoint H L) (hp : f∈preservers (Strip H L hd))
    {g : Steinberg n R} (hg : g∈Strip H L hd) : f g=g := by
  apply mul_inv_eq_one.mp
  apply strip_faithful H L hd ((Strip H L hd).mul_mem ((hp g).mpr hg) ((Strip H L hd).inv_mem hg))
  simp only [map_mul,map_inv,hf,mul_inv_cancel]

lemma identity_of_fixes_strips (t : Fin n) (f : MulAut (Steinberg n R))
    (hc : ∀g∈columnStrip t, f g=g) (hr : ∀g∈rowStrip t, f g=g) : f=1 := by
  have hh : f.toMonoidHom = MonoidHom.id _ := by
    apply Steinberg.hom_ext
    intro p a
    change f (x p a) = x p a
    by_cases hpt : p.row=t
    · have hp : p=⟨t,p.col,hpt ▸ p.ne⟩ := by cases p; cases hpt; rfl
      rw [hp]
      exact hr _ (row_root_mem t p.col (hpt ▸ p.ne) a)
    · by_cases hct : p.col=t
      · have hp : p=⟨p.row,t,hct ▸ p.ne⟩ := by cases p; cases hct; rfl
        rw [hp]
        exact hc _ (column_root_mem t p.row (hct ▸ p.ne) a)
      · have he := x_mul p.row t p.col hpt (Ne.symm hct) p.ne a (1:R)
        rw [mul_one] at he
        rw [←he]
        change f.toMonoidHom (bracket _ _) = bracket _ _
        rw [map_bracket]
        change bracket (f (x ⟨p.row,t,hpt⟩ a)) (f (x ⟨t,p.col,Ne.symm hct⟩ 1)) = _
        rw [hc _ (column_root_mem t p.row hpt a),hr _ (row_root_mem t p.col (Ne.symm hct) 1)]
  ext g
  exact DFunLike.congr_fun hh g

end

section
open Classical Steinberg MatrixGenerators Kernel
variable {n : ℕ} {R : Type*} [Ring R]

lemma supported_column (S : Finset (Fin n)) (t : Fin n) (ht : t∉S) :
    SmallPresentation.supported (R := R) S ≤ (preservers (columnStrip t)).comap wordAction := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change generatorAction g∈preservers (columnStrip t)
  cases g with
  | root i j h a =>
    have hi : i∈S := hg (by simp [SmallPresentation.Generator.support])
    have hj : j∈S := hg (by simp [SmallPresentation.Generator.support])
    exact conj_preserves_column t ⟨i,j,h⟩ (fun he => ht (he ▸ hi)) (fun he => ht (he ▸ hj)) a
  | diag i u => exact scale_preserves_strip _ _ _ _

lemma supported_row (S : Finset (Fin n)) (t : Fin n) (ht : t∉S) :
    SmallPresentation.supported (R := R) S ≤ (preservers (rowStrip t)).comap wordAction := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change generatorAction g∈preservers (rowStrip t)
  cases g with
  | root i j h a =>
    have hi : i∈S := hg (by simp [SmallPresentation.Generator.support])
    have hj : j∈S := hg (by simp [SmallPresentation.Generator.support])
    exact conj_preserves_row t ⟨i,j,h⟩ (fun he => ht (he ▸ hi)) (fun he => ht (he ▸ hj)) a
  | diag i u => exact scale_preserves_strip _ _ _ _

lemma supported_relation_trivial (S : Finset (Fin n)) (t : Fin n) (ht : t∉S)
    (w : FreeGroup (GLGenerator (n := n) (R := R))) (hw : w∈SmallPresentation.supported S)
    (he : SmallPresentation.matrixWord w=1) : wordAction w=1 := by
  have hf (g : Steinberg n R) : Elementary.representation (wordAction w g) = Elementary.representation g := by
    rw [word_equivariant,he]
    simp
  apply identity_of_fixes_strips t (wordAction w)
  · intro g hg
    exact fixes_strip (wordAction w) hf _ _ _ (supported_column S t ht hw) hg
  · intro g hg
    exact fixes_strip (wordAction w) hf _ _ _ (supported_row S t ht hw) hg

lemma small_relation_trivial (hn : 6≤n) (w : FreeGroup (GLGenerator (n := n) (R := R)))
    (hw : w∈SmallPresentation.relations) : wordAction w=1 := by
  obtain ⟨he,S,hS,hs⟩ := hw
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
    (by simpa using (by omega : S.card<n))
  exact supported_relation_trivial S t ht w hs he

def presentationAction (hn : 6≤n) : SmallPresentation.Group (ι := Fin n) (R := R) →* MulAut (Steinberg n R) :=
  PresentedGroup.toGroup (f := generatorAction) (fun w hw => small_relation_trivial hn w hw)

@[simp] lemma presentationAction_gen (hn : 6≤n) (g : GLGenerator (n := n) (R := R)) :
    presentationAction hn (SmallPresentation.gen g) = generatorAction g := PresentedGroup.toGroup.of _

end

open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom) (hn : 6≤n)

def matrixAction : (Matrix (Fin n) (Fin n) R)ˣ →* MulAut (Steinberg n R) :=
  (presentationAction hn).comp (SmallPresentation.equivalence ε hI (Fin n)).symm.toMonoidHom

lemma matrixAction_e (p : Root n) (a : R) :
    matrixAction ε hI hn (Elementary.e p a) = MulAut.conj (x p a) := by
  have he : SmallPresentation.equivalence ε hI (Fin n)
      (SmallPresentation.gen (.root p.row p.col p.ne a)) = Elementary.e p a := by
    rw [SmallPresentation.equivalence_apply,SmallPresentation.evaluate_gen]
    exact elementary_eq_e p a
  rw [←he]
  simp only [matrixAction,MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe,MulEquiv.symm_apply_apply,presentationAction_gen]
  rfl

lemma matrixAction_representation : (matrixAction ε hI hn).comp Elementary.representation =
    MulAut.conj (G := Steinberg n R) := by
  apply Steinberg.hom_ext
  intro p a
  simpa only [MonoidHom.comp_apply,Elementary.representation_x] using matrixAction_e ε hI hn p a

include ε hI hn in

theorem kernel_central : (Elementary.representation (n := n) (R := R)).ker ≤
    Subgroup.center (Steinberg n R) := by
  intro g hg
  have he : Elementary.representation g=1 := hg
  have hh := DFunLike.congr_fun (matrixAction_representation ε hI hn) g
  simp only [MonoidHom.comp_apply,he,map_one] at hh
  apply Subgroup.mem_center_iff.mpr
  intro h
  have hf := congrArg (fun f : MulAut (Steinberg n R) => f h) hh
  change h = g*h*g⁻¹ at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf.symm).symm

end SourceBurnside.Stability.SteinbergAction

end

namespace SourceBurnside.ConcreteSource

theorem kernel_central : (Elementary.representation (n := 12) (R := R)).ker ≤
    Subgroup.center (Steinberg 12 R) :=
  Stability.SteinbergAction.kernel_central augmentation matrix_nil_kernel (by decide)

theorem kernel_central_rank (n : ℕ) (hn : 6≤n) :
    (Elementary.representation (n := n) (R := R)).ker ≤ Subgroup.center (Steinberg n R) :=
  Stability.SteinbergAction.kernel_central augmentation matrix_nil_kernel hn

end SourceBurnside.ConcreteSource

end OAI
