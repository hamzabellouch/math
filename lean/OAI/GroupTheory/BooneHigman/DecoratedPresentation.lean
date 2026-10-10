import OAI.GroupTheory.BooneHigman.TreeRefinement

namespace OAI

noncomputable section

/-!
Stabilizer cocycles, decorations, and explicit finite endpoint relations.
-/

namespace FiniteAlgebraicEnvelopes.FiniteLocalizationClosure
universe u
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Group K] (f : K →* K) (a : K) (s : Finset K)
variable {r r' : Finset K} (h : r ⊆ r')
include h

lemma baseRelations_mono : baseRelations f a s r ⊆ baseRelations f a s r' :=
  Finset.union_subset_union h (Finset.Subset.refl _)

lemma relations_mono : relations f a s r ⊆ relations f a s r' :=
  Finset.union_subset_union (baseRelations_mono f a s h)
    (Finset.image_subset_image (baseRelations_mono f a s h))

lemma kernel_mono : kernel f a s r ≤ kernel f a s r' :=
  Subgroup.normalClosure_mono (relations_mono f a s h)

def quotientMap : Quotient f a s r →* Quotient f a s r' :=
  QuotientGroup.map _ _ (MonoidHom.id K) (kernel_mono f a s h)

lemma quotientMap_project (g : K) :
    quotientMap f a s h (project f a s r g)=project f a s r' g := rfl

lemma quotientMap_surjective : Function.Surjective (quotientMap f a s h) := by
  intro z
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨QuotientGroup.mk g,rfl⟩

lemma quotientMap_localization (hs : Subgroup.closure (s : Set K)=⊤) (z : Quotient f a s r) :
    quotientMap f a s h (localization f a s r hs z)=
      localization f a s r' hs (quotientMap f a s h z) := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective z
  change project f a s r g=z at hg
  rw [← hg,localization_project,quotientMap_project,quotientMap_project,localization_project]

end FiniteAlgebraicEnvelopes.FiniteLocalizationClosure

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))

/-- Finite structural laws together with the point stabilizer laws. -/
def decoratedRelations : Finset (Seed (Γ:=Γ) x) :=
  structuralRelations x s ∪ t.image (fixedWord x)

lemma decoratedRelations_valid : ∀ g∈decoratedRelations x s t,evaluation x g=1 := by
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact structuralRelations_valid x s g hg
  · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hg
    exact evaluation_fixedWord x k

abbrev DecoratedQuotient := LocalQuotient x s (decoratedRelations x s t)

instance decoratedQuotient_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (DecoratedQuotient x s t) := inferInstance

def decoratedEvaluation : DecoratedQuotient x s t →* group (Γ:=Γ) (X:=X) :=
  localEvaluation x s _ (decoratedRelations_valid x s t)

lemma decoratedEvaluation_surjective : Function.Surjective (decoratedEvaluation x s t) :=
  localEvaluation_surjective x s _ (decoratedRelations_valid x s t)

def decoratedProject : Seed (Γ:=Γ) x →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.project _ _ _ _

def structuralToDecorated : StructuralQuotient x s →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.quotientMap _ _ _ (Finset.subset_union_left)

lemma structuralToDecorated_project (g : Seed (Γ:=Γ) x) :
    structuralToDecorated x s t (structuralProject x s g)=decoratedProject x s t g := rfl

def decoratedRoot : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (rootWord x)
def decoratedHalf : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (halfWord x)
def decoratedRight : Γ →* DecoratedQuotient x s t := (decoratedProject x s t).comp (rightWord x)

variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
include hs

lemma decorated_commute (g h : Γ) :
    Commute (decoratedHalf x s t g) (decoratedRight x s t h) := by
  have hc := (structuralProject_comm_all x s hs (rootWord x g) (rootWord x h)).map
    (structuralToDecorated x s t)
  exact hc

def decoratedDiagonal : Γ →* DecoratedQuotient x s t where
  toFun g := decoratedHalf x s t g * decoratedRight x s t g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    exact ((decorated_commute x s t hs h g).symm.mul_mul_mul_comm _ _).symm

lemma decorated_fixed {g : MulAction.stabilizer Γ x} (hg : g∈t) :
    decoratedRoot x s t g.val=decoratedDiagonal x s t hs g.val := by
  have hm : fixedWord x g∈decoratedRelations x s t :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)
  have hp := FiniteLocalizationClosure.project_base (localizationSeed x) (associatorWord x)
    s (decoratedRelations x s t) (Finset.mem_union_left _ hm)
  change decoratedProject x s t (rootWord x g.val * (halfWord x g.val * rightWord x g.val)⁻¹)=1 at hp
  simp only [map_mul,map_inv] at hp
  exact mul_inv_eq_one.mp hp

lemma decorated_fixed_all (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
    (g : MulAction.stabilizer Γ x) :
    decoratedRoot x s t g.val=decoratedDiagonal x s t hs g.val := by
  have he : (decoratedRoot x s t).comp (MulAction.stabilizer Γ x).subtype=
      (decoratedDiagonal x s t hs).comp (MulAction.stabilizer Γ x).subtype := by
    apply MonoidHom.eq_of_eqOn_dense ht
    intro k hk
    exact decorated_fixed x s t hs hk
  exact DFunLike.congr_fun he g

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.StabilizerCocycle
universe u v w
variable {Γ : Type u} {X : Type v} {H : Type w}
variable [Group Γ] [MulAction Γ X] [Group H]
variable (x : X) (R D : Γ →* H)
variable (hfixed : ∀ k : MulAction.stabilizer Γ x,R k.val=D k.val)
include hfixed

/-- The difference of two copies of the acting group descends to its orbit
when those copies agree on the point stabilizer. -/
lemma equal_of_smul_eq {g h : Γ} (he : g • x=h • x) :
    R g * (D g)⁻¹=R h * (D h)⁻¹ := by
  have hk : h⁻¹*g∈MulAction.stabilizer Γ x := by
    change (h⁻¹*g) • x=x
    rw [mul_smul,he,inv_smul_smul]
  have hf := hfixed ⟨h⁻¹*g,hk⟩
  change R (h⁻¹*g)=D (h⁻¹*g) at hf
  simp only [map_mul,map_inv] at hf
  have hr : R g=R h*((D h)⁻¹*D g) := by
    rw [← hf]
    group
  rw [hr]
  group

variable [MulAction.IsPretransitive Γ X]

omit hfixed in
/-- The orbit-indexed difference; the selected representative is immaterial. -/
def value (y : X) : H :=
  let g := (MulAction.exists_smul_eq Γ x y).choose
  R g * (D g)⁻¹

lemma value_smul (g : Γ) : value x R D (g • x)=R g*(D g)⁻¹ :=
  equal_of_smul_eq x R D hfixed (MulAction.exists_smul_eq Γ x (g • x)).choose_spec

lemma value_base : value x R D x=1 := by
  simpa only [one_smul,map_one,inv_one,mul_one] using value_smul x R D hfixed (1 : Γ)

/-- Exact covariance of the orbit-indexed difference. -/
lemma covariance (g : Γ) (y : X) :
    R g*value x R D y=value x R D (g • y)*D g := by
  obtain ⟨h,rfl⟩ := MulAction.exists_smul_eq Γ x y
  rw [← mul_smul,value_smul x R D hfixed,value_smul x R D hfixed]
  simp only [map_mul,mul_inv_rev]
  group

end FiniteAlgebraicEnvelopes.StabilizerCocycle

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)
variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)

/-- A baker element defined inside the finitely presented quotient, before
any injectivity or table-presentation completeness theorem. -/
def decoratedBaker (y : X) : DecoratedQuotient x s t :=
  StabilizerCocycle.value x (decoratedRoot x s t) (decoratedDiagonal x s t hs) y

include ht
lemma decoratedBaker_smul (g : Γ) :
    decoratedBaker x s t hs (g • x)=
      decoratedRoot x s t g*(decoratedDiagonal x s t hs g)⁻¹ :=
  StabilizerCocycle.value_smul x _ _ (decorated_fixed_all x s t hs ht) g

lemma decoratedBaker_base : decoratedBaker x s t hs x=1 :=
  StabilizerCocycle.value_base x _ _ (decorated_fixed_all x s t hs ht)

/-- The complete colour covariance family follows from the finite stabilizer
relations. It is not imposed once for each point of the infinite set. -/
lemma decoratedBaker_covariance (g : Γ) (y : X) :
    decoratedRoot x s t g*decoratedBaker x s t hs y=
      decoratedBaker x s t hs (g • y)*decoratedDiagonal x s t hs g :=
  StabilizerCocycle.covariance x _ _ (decorated_fixed_all x s t hs ht) g y

omit ht in
lemma decoratedEvaluation_project (g : Seed (Γ:=Γ) x) :
    decoratedEvaluation x s t (decoratedProject x s t g)=evaluation x g := rfl

omit ht in
lemma decoratedEvaluation_diagonal (g : Γ) :
    decoratedEvaluation x s t (decoratedDiagonal x s t hs g)=diagonal x (embedding g) := by
  change decoratedEvaluation x s t (decoratedProject x s t (halfWord x g) *
    decoratedProject x s t (rightWord x g))=_
  rw [map_mul,decoratedEvaluation_project,decoratedEvaluation_project,
    evaluation_halfWord,evaluation_rightWord]
  rfl

/-- The internally descended baker evaluates to the literal coordinate baker. -/
lemma decoratedEvaluation_baker (y : X) :
    decoratedEvaluation x s t (decoratedBaker x s t hs y)=baker x y := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq Γ x y
  rw [decoratedBaker_smul x s t hs ht,map_mul,map_inv,decoratedEvaluation_diagonal]
  change evaluation x (rootWord x g)*(diagonal x (embedding g))⁻¹=baker x (g • x)
  rw [evaluation_rootWord,← baker_inverse, baker_smul,mul_inv_rev,inv_inv]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

lemma decoratedProject_surjective : Function.Surjective (decoratedProject (Γ:=Γ) x s t) :=
  QuotientGroup.mk_surjective

lemma structuralToDecorated_surjective : Function.Surjective (structuralToDecorated (Γ:=Γ) x s t) :=
  FiniteLocalizationClosure.quotientMap_surjective _ _ _ _

def decoratedLocalization : DecoratedQuotient x s t →* DecoratedQuotient x s t :=
  FiniteLocalizationClosure.localization _ _ _ _ hs

def decoratedRightLocalization : DecoratedQuotient x s t →* DecoratedQuotient x s t :=
  (MulAut.conj (decoratedProject x s t (flipWord x))).toMonoidHom.comp
    (decoratedLocalization x s t hs)

lemma decoratedLocalization_project (g : Seed (Γ:=Γ) x) :
    decoratedLocalization x s t hs (decoratedProject x s t g)=
      decoratedProject x s t (localizationSeed x g) := rfl

lemma decoratedRightLocalization_project (g : Seed (Γ:=Γ) x) :
    decoratedRightLocalization x s t hs (decoratedProject x s t g)=
      decoratedProject x s t (rightLocalizationSeed x g) := by
  change decoratedProject x s t (flipWord x) * decoratedProject x s t (localizationSeed x g) *
    (decoratedProject x s t (flipWord x))⁻¹=decoratedProject x s t
      (flipWord x * localizationSeed x g * (flipWord x)⁻¹)
  simp only [map_mul,map_inv]

lemma decoratedLocalizations_commute (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    Commute (decoratedLocalization x s t hs g) (decoratedRightLocalization x s t hs h) := by
  obtain ⟨g,rfl⟩ := decoratedProject_surjective x s t g
  obtain ⟨h,rfl⟩ := decoratedProject_surjective x s t h
  rw [decoratedLocalization_project,decoratedRightLocalization_project]
  exact (structuralProject_comm_all x s hs g h).map (structuralToDecorated x s t)

def decoratedTensor : DecoratedQuotient (Γ:=Γ) x s t × DecoratedQuotient x s t →*
    DecoratedQuotient x s t :=
  (decoratedLocalization x s t hs).noncommCoprod (decoratedRightLocalization x s t hs)
    (decoratedLocalizations_commute x s t hs)

lemma decoratedTensor_apply (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedTensor x s t hs (g,h)=decoratedLocalization x s t hs g *
      decoratedRightLocalization x s t hs h := rfl

lemma decoratedDiagonal_tensor (g : Γ) :
    decoratedDiagonal x s t hs g=decoratedTensor x s t hs
      (decoratedRoot x s t g,decoratedRoot x s t g) := rfl

lemma structuralToDecorated_localization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralLocalization x s hs g)=
      decoratedLocalization x s t hs (structuralToDecorated x s t g) :=
  FiniteLocalizationClosure.quotientMap_localization _ _ _ _ hs g

lemma structuralToDecorated_rightLocalization (g : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralRightLocalization x s hs g)=
      decoratedRightLocalization x s t hs (structuralToDecorated x s t g) := by
  change structuralToDecorated x s t (structuralSymmetry x s * structuralLocalization x s hs g *
    (structuralSymmetry x s)⁻¹)=_
  rw [map_mul,map_mul,map_inv,structuralToDecorated_localization]
  rfl

lemma structuralToDecorated_tensor (g h : StructuralQuotient (Γ:=Γ) x s) :
    structuralToDecorated x s t (structuralTensor x s hs (g,h))=
      decoratedTensor x s t hs (structuralToDecorated x s t g,structuralToDecorated x s t h) := by
  simp only [structuralTensor_apply,decoratedTensor_apply,map_mul,
    structuralToDecorated_localization,structuralToDecorated_rightLocalization]

/-- A binary tensor at any colour, constructed internally from the descended baker. -/
def decoratedColourTensor (y : X) : DecoratedQuotient (Γ:=Γ) x s t × DecoratedQuotient x s t →*
    DecoratedQuotient x s t :=
  (MulAut.conj (decoratedBaker x s t hs y)).toMonoidHom.comp (decoratedTensor x s t hs)

lemma decoratedColourTensor_apply (y : X) (g h : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedColourTensor x s t hs y (g,h)=decoratedBaker x s t hs y *
      decoratedTensor x s t hs (g,h)*(decoratedBaker x s t hs y)⁻¹ := rfl

variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
include ht

/-- The full label/split naturality law follows internally from the finite
stabilizer relations, rather than being assumed as an infinite relator family. -/
lemma decoratedColourTensor_covariance (g : Γ) (y : X) (a b : DecoratedQuotient (Γ:=Γ) x s t) :
    decoratedRoot x s t g * decoratedColourTensor x s t hs y (a,b) *
      (decoratedRoot x s t g)⁻¹ = decoratedColourTensor x s t hs (g • y)
        (decoratedRoot x s t g*a*(decoratedRoot x s t g)⁻¹,
         decoratedRoot x s t g*b*(decoratedRoot x s t g)⁻¹) := by
  let R := decoratedRoot x s t g
  let D := decoratedDiagonal x s t hs g
  have hD : D=decoratedTensor x s t hs (R,R) := decoratedDiagonal_tensor x s t hs g
  have hc : R*decoratedBaker x s t hs y=decoratedBaker x s t hs (g • y)*D :=
    decoratedBaker_covariance x s t hs ht g y
  have hn : decoratedTensor x s t hs (R*a*R⁻¹,R*b*R⁻¹)=
      D*decoratedTensor x s t hs (a,b)*D⁻¹ := by
    rw [hD]
    change decoratedTensor x s t hs (((R,R)*(a,b))*(R,R)⁻¹)=_
    rw [map_mul,map_mul,map_inv]
  change R*(decoratedBaker x s t hs y*decoratedTensor x s t hs (a,b)*
    (decoratedBaker x s t hs y)⁻¹)*R⁻¹=_
  rw [decoratedColourTensor_apply,hn]
  calc
    _=(R*decoratedBaker x s t hs y)*decoratedTensor x s t hs (a,b)*
      (R*decoratedBaker x s t hs y)⁻¹ := by group
    _=_ := by rw [hc]; group

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

def bakerWord (y : X) : Seed (Γ:=Γ) x :=
  let g := (MulAction.exists_smul_eq Γ x y).choose
  rootWord x g*(halfWord x g*rightWord x g)⁻¹

lemma evaluation_bakerWord (y : X) : evaluation (Γ:=Γ) x (bakerWord x y)=baker x y := by
  let g := (MulAction.exists_smul_eq Γ x y).choose
  have hg : g • x=y := (MulAction.exists_smul_eq Γ x y).choose_spec
  change evaluation x (rootWord x g*(halfWord x g*rightWord x g)⁻¹)=_
  rw [map_mul,map_inv,map_mul,evaluation_rootWord,evaluation_halfWord,evaluation_rightWord]
  change embedding g*(diagonal x (embedding g))⁻¹=baker x y
  rw [← hg,← baker_inverse,baker_smul,mul_inv_rev,inv_inv]

def middleSwapWord : Seed (Γ:=Γ) x :=
  associatorWord x * rightLocalizationSeed x
    ((associatorWord x)⁻¹*localizationSeed x (flipWord x)*associatorWord x) * (associatorWord x)⁻¹

def middleSwapMove : Move (Γ:=Γ) x
    (.split x (.split x .leaf .leaf) (.split x .leaf .leaf))
    (.split x (.split x .leaf .leaf) (.split x .leaf .leaf)) :=
  let l : Tree X := .leaf
  let a := Move.rotate (Γ:=Γ) x l l (.split x l l)
  let b := (Move.refl (Γ:=Γ) (x:=x) l).join (Move.rotate x l l l) x
  let c := (Move.refl (Γ:=Γ) (x:=x) l).join
    ((Move.exchange x l l).join (Move.refl l) x) x
  (((a.symm.trans b).trans c).trans b.symm).trans a

lemma evaluation_middleSwapWord : evaluation (Γ:=Γ) x (middleSwapWord x)=(middleSwapMove x).element := by
  simp only [middleSwapWord,map_mul,map_inv,evaluation_associatorWord,
    evaluation_rightLocalizationSeed,evaluation_localizationSeed,evaluation_flipWord]
  simp only [middleSwapMove,Move.trans,Move.symm,Move.rotate,Move.join,Move.refl,
    Move.exchange,sumElement,map_one,one_mul,mul_one]
  group

lemma middleSwap_attach (b c : Bool) (z : Cube X) :
    (evaluation (Γ:=Γ) x (middleSwapWord x)).val
      ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach z))=
      (Prefix.oneBit x c).attach ((Prefix.oneBit x b).attach z) := by
  rw [evaluation_middleSwapWord]
  cases b <;> cases c
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inl (Sum.inl PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inl (Sum.inl PUnit.unit))=
        Sum.inl (Sum.inl PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inl (Sum.inr PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inl (Sum.inr PUnit.unit))=
        Sum.inr (Sum.inl PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inr (Sum.inl PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inr (Sum.inl PUnit.unit))=
        Sum.inl (Sum.inr PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh
  · have hh := (middleSwapMove (Γ:=Γ) x).chart (Sum.inr (Sum.inr PUnit.unit)) z
    have hi : (middleSwapMove (Γ:=Γ) x).leaves (Sum.inr (Sum.inr PUnit.unit))=
        Sum.inr (Sum.inr PUnit.unit) := rfl
    rw [hi] at hh
    simpa only [Tree.brick,Prefix.comp_attach,Prefix.empty_attach] using hh

def gridWord (y z : X) : Seed (Γ:=Γ) x :=
  bakerWord x y * (localizationSeed x (bakerWord x z) * rightLocalizationSeed x (bakerWord x z))

lemma evaluation_gridWord (y z : X) : evaluation (Γ:=Γ) x (gridWord x y z)=
    baker x y*sumElement x (baker x z) (baker x z) := by
  simp only [gridWord,map_mul,evaluation_bakerWord,evaluation_localizationSeed,
    evaluation_rightLocalizationSeed,sumElement,left,right]

lemma gridWord_attach (y z : X) (b c : Bool) (w : Cube X) :
    (evaluation (Γ:=Γ) x (gridWord x y z)).val
      ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      (Prefix.oneBit y b).attach ((Prefix.oneBit z c).attach w) := by
  rw [evaluation_gridWord]
  change (baker (Γ:=Γ) x y).val ((sumElement x (baker x z) (baker x z)).val
    ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w)))=_
  cases b <;> simp only [sumElement_left,sumElement_right,baker_attach]

/-- One coordinate-interchange relation, between the two literal grids. -/
def interchangeWord (y z : X) : Seed (Γ:=Γ) x :=
  gridWord x y z*(gridWord x z y*middleSwapWord x)⁻¹

omit [MulAction.IsPretransitive Γ X] in
lemma eq_of_doubleBit (f g : group (Γ:=Γ) (X:=X))
    (h : ∀ b c w,f.val ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      g.val ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))) : f=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  obtain ⟨b,⟨v,rfl⟩,_⟩ := (Partition.bit x).cover w
  obtain ⟨c,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover v
  exact h b c w

lemma grid_interchange {y z : X} (hyz : y≠z) :
    evaluation (Γ:=Γ) x (gridWord x y z)=
      evaluation x (gridWord x z y)*evaluation x (middleSwapWord x) := by
  apply eq_of_doubleBit x
  intro b c w
  change (evaluation (Γ:=Γ) x (gridWord x y z)).val
    ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w))=
      (evaluation (Γ:=Γ) x (gridWord x z y)).val
        ((evaluation x (middleSwapWord x)).val
          ((Prefix.oneBit x b).attach ((Prefix.oneBit x c).attach w)))
  rw [middleSwap_attach,gridWord_attach,gridWord_attach]
  rw [← Prefix.comp_attach,← Prefix.comp_attach,Prefix.oneBit_comp_comm hyz]

lemma evaluation_interchangeWord {y z : X} (hyz : y≠z) :
    evaluation (Γ:=Γ) x (interchangeWord x y z)=1 := by
  simp only [interchangeWord,map_mul,map_inv]
  rw [grid_interchange x hyz,mul_inv_cancel]

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

def halfAssociatorBinding : Seed (Γ:=Γ) x :=
  generatorWord x ⟨localize (left x) (associator x),by simp [finiteSet]⟩ *
    (localizationSeed x (associatorWord x))⁻¹

def halfFlipBinding : Seed (Γ:=Γ) x :=
  generatorWord x ⟨localize (left x) (flip x),by simp [finiteSet]⟩ *
    (localizationSeed x (flipWord x))⁻¹

lemma evaluation_halfAssociatorBinding : evaluation (Γ:=Γ) x (halfAssociatorBinding x)=1 := by
  simp only [halfAssociatorBinding,map_mul,map_inv,evaluation_generatorWord,
    evaluation_localizationSeed,evaluation_associatorWord,mul_inv_cancel]

lemma evaluation_halfFlipBinding : evaluation (Γ:=Γ) x (halfFlipBinding x)=1 := by
  simp only [halfFlipBinding,map_mul,map_inv,evaluation_generatorWord,
    evaluation_localizationSeed,evaluation_flipWord,mul_inv_cancel]

variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x)) (y : X)

/-- Explicit finite presentation candidate: structure, stabilizer, generator
bindings, and one orbit representative of distinct-colour interchange.
Its completeness is not built into this definition. -/
def endpointRelations : Finset (Seed (Γ:=Γ) x) :=
  decoratedRelations x s t ∪ {halfAssociatorBinding x,halfFlipBinding x,interchangeWord x x y}

lemma endpointRelations_valid (hxy : x≠y) :
    ∀ g∈endpointRelations x s t y,evaluation x g=1 := by
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact decoratedRelations_valid x s t g hg
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl
    · exact evaluation_halfAssociatorBinding x
    · exact evaluation_halfFlipBinding x
    · exact evaluation_interchangeWord x hxy

/-- A finite presentation with a surjection to the concrete simple table group. -/

abbrev EndpointQuotient := LocalQuotient x s (endpointRelations x s t y)

instance endpointQuotient_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (EndpointQuotient x s t y) := inferInstance

def endpointEvaluation (hxy : x≠y) : EndpointQuotient x s t y →* group (Γ:=Γ) (X:=X) :=
  localEvaluation x s _ (endpointRelations_valid x s t y hxy)

lemma endpointEvaluation_surjective (hxy : x≠y) :
    Function.Surjective (endpointEvaluation x s t y hxy) :=
  localEvaluation_surjective x s _ (endpointRelations_valid x s t y hxy)

def endpointProject : Seed (Γ:=Γ) x →* EndpointQuotient x s t y :=
  FiniteLocalizationClosure.project _ _ _ _

def decoratedToEndpoint : DecoratedQuotient x s t →* EndpointQuotient x s t y :=
  FiniteLocalizationClosure.quotientMap _ _ _ (Finset.subset_union_left)

lemma decoratedToEndpoint_project (g : Seed (Γ:=Γ) x) :
    decoratedToEndpoint x s t y (decoratedProject x s t g)=endpointProject x s t y g := rfl

lemma endpointProject_rel {g : Seed (Γ:=Γ) x} (hg : g∈endpointRelations x s t y) :
    endpointProject x s t y g=1 :=
  FiniteLocalizationClosure.project_base _ _ _ _ (Finset.mem_union_left _ hg)

lemma endpoint_halfAssociatorBinding : endpointProject x s t y
    (generatorWord x ⟨localize (left x) (associator x),by simp [finiteSet]⟩)=
      endpointProject x s t y (localizationSeed x (associatorWord x)) := by
  have h := endpointProject_rel x s t y
    (show halfAssociatorBinding (Γ:=Γ) x∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  change endpointProject x s t y (_*_⁻¹)=1 at h
  rw [map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma endpoint_halfFlipBinding : endpointProject x s t y
    (generatorWord x ⟨localize (left x) (flip x),by simp [finiteSet]⟩)=
      endpointProject x s t y (localizationSeed x (flipWord x)) := by
  have h := endpointProject_rel x s t y
    (show halfFlipBinding (Γ:=Γ) x∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  change endpointProject x s t y (_*_⁻¹)=1 at h
  rw [map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

lemma endpoint_interchange : endpointProject x s t y (gridWord x x y)=
    endpointProject x s t y (gridWord x y x)*endpointProject x s t y (middleSwapWord x) := by
  have h := endpointProject_rel x s t y
    (show interchangeWord (Γ:=Γ) x x y∈endpointRelations x s t y from
      Finset.mem_union_right _ (by simp))
  simp only [interchangeWord,map_mul,map_inv] at h
  exact mul_inv_eq_one.mp h

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]
variable (s : Finset (Seed (Γ:=Γ) x)) (t : Finset (MulAction.stabilizer Γ x))
variable (hs : Subgroup.closure (s : Set (Seed (Γ:=Γ) x))=⊤)

def decoratedGrid (y z : X) : DecoratedQuotient x s t :=
  decoratedBaker x s t hs y*decoratedTensor x s t hs
    (decoratedBaker x s t hs z,decoratedBaker x s t hs z)

lemma decoratedProject_bakerWord (y : X) :
    decoratedProject x s t (bakerWord x y)=decoratedBaker x s t hs y := by
  simp only [bakerWord,map_mul,map_inv]
  rfl

lemma decoratedProject_gridWord (y z : X) :
    decoratedProject x s t (gridWord x y z)=decoratedGrid x s t hs y z := by
  simp only [gridWord,map_mul]
  rw [← decoratedLocalization_project x s t hs,← decoratedRightLocalization_project x s t hs,
    decoratedProject_bakerWord,decoratedProject_bakerWord]
  rfl

variable (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
include ht

/-- A label at the root passes through a two-colour grid as four identical
leaf labels. All colours here are arbitrary; only finite stabilizer laws were used. -/
lemma decoratedGrid_covariance (g : Γ) (y z : X) :
    decoratedRoot x s t g*decoratedGrid x s t hs y z=
      decoratedGrid x s t hs (g • y) (g • z)*decoratedTensor x s t hs
        (decoratedDiagonal x s t hs g,decoratedDiagonal x s t hs g) := by
  let B := decoratedBaker x s t hs
  let T := decoratedTensor x s t hs
  let R := decoratedRoot x s t g
  let D := decoratedDiagonal x s t hs g
  have hc (y : X) : R*B y=B (g • y)*D := decoratedBaker_covariance x s t hs ht g y
  have hd : D=T (R,R) := decoratedDiagonal_tensor x s t hs g
  have hm₁ : D*T (B z,B z)=T (R*B z,R*B z) := by
    rw [hd]
    exact (map_mul T (R,R) (B z,B z)).symm
  have hm₂ : T (B (g • z)*D,B (g • z)*D)=T (B (g • z),B (g • z))*T (D,D) :=
    map_mul T (B (g • z),B (g • z)) (D,D)
  change R*(B y*T (B z,B z))=(B (g • y)*T (B (g • z),B (g • z)))*T (D,D)
  rw [← mul_assoc,hc,mul_assoc,hm₁,hc,hm₂,mul_assoc]

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
