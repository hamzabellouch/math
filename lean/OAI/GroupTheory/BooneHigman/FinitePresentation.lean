import OAI.GroupTheory.BooneHigman.Generators

namespace OAI

noncomputable section

/-!
Finite presentation seeds, localization, and structural relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

/-- An actual finitely presented source for the finite-table group. The two
copies of Γ map to the root and one half-cube, and the free factor maps to the
four explicit untwisted generators. Its quotient kernel is a construction,
not an extra main-theorem hypothesis. -/
def Seed := Monoid.Coprod (Monoid.Coprod Γ Γ)
  (FreeGroup (finiteSet (Γ:=Γ) x))

instance : Group (Seed (Γ:=Γ) x) :=
  inferInstanceAs (Group (Monoid.Coprod (Monoid.Coprod Γ Γ)
    (FreeGroup (finiteSet (Γ:=Γ) x))))

instance seed_finitelyPresented [Group.IsFinitelyPresented Γ] :
    Group.IsFinitelyPresented (Seed (Γ:=Γ) x) :=
  inferInstanceAs (Group.IsFinitelyPresented (Monoid.Coprod (Monoid.Coprod Γ Γ)
    (FreeGroup (finiteSet (Γ:=Γ) x))))

def evaluation : Seed (Γ:=Γ) x →* group (Γ:=Γ) (X:=X) :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift embedding ((localize (left x)).comp embedding))
    (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val))

lemma evaluation_range : (evaluation (Γ:=Γ) x).range=subgroup x := by
  change (Monoid.Coprod.lift
    (Monoid.Coprod.lift embedding ((localize (left x)).comp embedding))
    (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val))).range=_
  rw [Monoid.Coprod.range_lift,Monoid.Coprod.range_lift]
  change _ ⊔ _ ⊔ (FreeGroup.lift (fun a : finiteSet (Γ:=Γ) x => a.val)).range =
    _ ⊔ _ ⊔ Subgroup.closure (finiteSet (Γ:=Γ) x : Set (group (Γ:=Γ) (X:=X)))
  congr 1
  exact (FreeGroup.closure_eq_range (finiteSet (Γ:=Γ) x : Set (group (Γ:=Γ) (X:=X)))).symm

lemma evaluation_surjective [MulAction.IsPretransitive Γ X] :
    Function.Surjective (evaluation (Γ:=Γ) x) := by
  rw [← MonoidHom.range_eq_top,evaluation_range,subgroup_eq_top]

/-- The exact quotient already known to be the desired concrete simple group.
Only finite normal generation of this explicitly defined kernel remains for
finite presentation; neither that property nor a main theorem is asserted here. -/
def quotientEquivalence [MulAction.IsPretransitive Γ X] :
    (Seed (Γ:=Γ) x ⧸ (evaluation x).ker) ≃* group (Γ:=Γ) (X:=X) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (evaluation_surjective x)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma half_copies_commute (x : X) (f h : group (Γ:=Γ) (X:=X)) :
    Commute (localize (Prefix.oneBit x false) f) (localize (Prefix.oneBit x true) h) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change localizePerm (Prefix.oneBit x false) f.val
      (localizePerm (Prefix.oneBit x true) h.val ((Prefix.oneBit x b).attach w))=
    localizePerm (Prefix.oneBit x true) h.val
      (localizePerm (Prefix.oneBit x false) f.val ((Prefix.oneBit x b).attach w))
  cases b
  · rw [localizePerm_outside _ _ (oneBit_outside x Bool.false_ne_true w),
      localizePerm_attach,
      localizePerm_outside _ _ (oneBit_outside x Bool.false_ne_true (f.val w))]
  · rw [localizePerm_attach,
      localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) (h.val w)),
      localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) w),
      localizePerm_attach]

lemma embedding_eq_diagonal_of_fixed (x : X) (g : Γ) (hg : g • x=x) :
    embedding (X:=X) g=diagonal x (embedding g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change twist g ((Prefix.oneBit x b).attach w)=_
  rw [twist_attach,twistPrefix_oneBit,hg,diagonal_attach]
  rfl

namespace Generators
variable (x : X)

def rootWord : Γ →* Seed (Γ:=Γ) x := Monoid.Coprod.inl.comp Monoid.Coprod.inl
def halfWord : Γ →* Seed (Γ:=Γ) x := Monoid.Coprod.inl.comp Monoid.Coprod.inr

def flipWord : Seed (Γ:=Γ) x :=
  Monoid.Coprod.inr (FreeGroup.of (⟨flip x,by simp [finiteSet]⟩ : finiteSet (Γ:=Γ) x))

def rightWord : Γ →* Seed (Γ:=Γ) x :=
  (MulAut.conj (flipWord (Γ:=Γ) x)).toMonoidHom.comp (halfWord x)

@[simp] lemma evaluation_rootWord (g : Γ) : evaluation (Γ:=Γ) x (rootWord x g)=embedding g := by
  rfl
@[simp] lemma evaluation_halfWord (g : Γ) :
    evaluation (Γ:=Γ) x (halfWord x g)=localize (left x) (embedding g) := by
  rfl
@[simp] lemma evaluation_flipWord : evaluation (Γ:=Γ) x (flipWord (Γ:=Γ) x)=flip x := by
  rfl
@[simp] lemma evaluation_rightWord (g : Γ) :
    evaluation (Γ:=Γ) x (rightWord x g)=localize (right x) (embedding g) := by
  change evaluation (Γ:=Γ) x (flipWord x * halfWord x g * (flipWord x)⁻¹)=_
  rw [map_mul,map_mul,map_inv,evaluation_flipWord,evaluation_halfWord]
  exact localize_conj (flip x) (flip_left x) (embedding g)

/-- The commutation relator for the two different halves. -/
def commutingWord (g h : Γ) : Seed (Γ:=Γ) x :=
  halfWord x g * rightWord x h * (halfWord x g)⁻¹ * (rightWord x h)⁻¹

/-- A point-stabilizer relation: its root copy equals its two half-copies. -/
def fixedWord (g : MulAction.stabilizer Γ x) : Seed (Γ:=Γ) x :=
  rootWord x g.val * (halfWord x g.val * rightWord x g.val)⁻¹

lemma evaluation_commutingWord (g h : Γ) : evaluation (Γ:=Γ) x (commutingWord x g h)=1 := by
  simp only [commutingWord,map_mul,map_inv,evaluation_halfWord,evaluation_rightWord]
  rw [(half_copies_commute x (embedding g) (embedding h)).eq]
  group

lemma evaluation_fixedWord (g : MulAction.stabilizer Γ x) : evaluation (Γ:=Γ) x (fixedWord x g)=1 := by
  simp only [fixedWord,map_mul,map_inv,evaluation_rootWord,evaluation_halfWord,evaluation_rightWord]
  conv_lhs => arg 1; rw [embedding_eq_diagonal_of_fixed x g.val g.property]
  change diagonal x (embedding g.val) * (diagonal x (embedding g.val))⁻¹=1
  exact mul_inv_cancel _

/-- Two finite families of genuine evaluation-kernel relations. Completeness
of these (plus the necessary tree-interchange and V relations) is NOT asserted. -/
def finiteRelations (s : Finset Γ) (t : Finset (MulAction.stabilizer Γ x)) :
    Finset (Seed (Γ:=Γ) x) :=
  (s ×ˢ s).image (fun gh => commutingWord x gh.1 gh.2) ∪ t.image (fixedWord x)

lemma finiteRelations_mem_ker (s : Finset Γ) (t : Finset (MulAction.stabilizer Γ x)) :
    (finiteRelations x s t : Set (Seed (Γ:=Γ) x)) ⊆ ((evaluation (Γ:=Γ) x).ker : Set (Seed (Γ:=Γ) x)) := by
  intro a ha
  simp only [finiteRelations,Finset.mem_coe,Finset.mem_union,Finset.mem_image] at ha
  rcases ha with ⟨⟨g,h⟩,_,rfl⟩|⟨g,_,rfl⟩
  · exact evaluation_commutingWord x g h
  · exact evaluation_fixedWord x g

lemma finiteRelations_closure_le_ker (s : Finset Γ) (t : Finset (MulAction.stabilizer Γ x)) :
    Subgroup.normalClosure (finiteRelations x s t : Set (Seed (Γ:=Γ) x)) ≤
      (evaluation (Γ:=Γ) x).ker :=
  Subgroup.normalClosure_le_normal (finiteRelations_mem_ker x s t)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable

lemma commute_homs_of_generators {K H : Type*} [Group K] [Group H]
    (s : Set K) (hs : Subgroup.closure s=⊤) (a b : K →* H)
    (h : ∀ i∈s,∀ j∈s,Commute (a i) (b j)) (g k : K) : Commute (a g) (b k) := by
  have hg : g∈Subgroup.closure s := by rw [hs]; trivial
  have hk : k∈Subgroup.closure s := by rw [hs]; trivial
  refine Subgroup.closure_induction₂ (p:=fun g k _ _ => Commute (a g) (b k))
    (fun i j hi hj => h i hi j hj) ?_ ?_ ?_ ?_ ?_ ?_ hg hk
  · intro z _; simpa only [map_one] using Commute.one_left (b z)
  · intro z _; simpa only [map_one] using Commute.one_right (a z)
  · intro i j z _ _ _ hi hj
    simpa only [map_mul] using hi.mul_left hj
  · intro i j z _ _ _ hi hj
    simpa only [map_mul] using hi.mul_right hj
  · intro i j _ _ hi
    simpa only [map_inv] using hi.inv_left
  · intro i j _ _ hi
    simpa only [map_inv] using hi.inv_right

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) (s : Finset Γ) (t : Finset (MulAction.stabilizer Γ x))

def relationKernel : Subgroup (Seed (Γ:=Γ) x) :=
  Subgroup.normalClosure (finiteRelations x s t : Set (Seed (Γ:=Γ) x))
instance : (relationKernel x s t).Normal := Subgroup.normalClosure_normal
abbrev RelationQuotient := Seed (Γ:=Γ) x ⧸ relationKernel x s t

def projection : Seed (Γ:=Γ) x →* RelationQuotient x s t :=
  QuotientGroup.mk' (relationKernel x s t)

def projectedRoot : Γ →* RelationQuotient x s t := (projection x s t).comp (rootWord x)
def projectedHalf : Γ →* RelationQuotient x s t := (projection x s t).comp (halfWord x)
def projectedRight : Γ →* RelationQuotient x s t := (projection x s t).comp (rightWord x)

lemma projection_rel {r : Seed (Γ:=Γ) x} (hr : r∈finiteRelations x s t) :
    projection x s t r=1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hr)

lemma projected_commute {g h : Γ} (hg : g∈s) (hh : h∈s) :
    Commute (projectedHalf x s t g) (projectedRight x s t h) := by
  have hrel : commutingWord x g h∈finiteRelations x s t := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(g,h),Finset.mem_product.mpr ⟨hg,hh⟩,rfl⟩
  have hp := projection_rel x s t hrel
  change projection x s t (halfWord x g * rightWord x h * (halfWord x g)⁻¹ * (rightWord x h)⁻¹)=1 at hp
  simp only [map_mul,map_inv] at hp
  change projectedHalf x s t g * projectedRight x s t h * (projectedHalf x s t g)⁻¹ *
    (projectedRight x s t h)⁻¹=1 at hp
  apply mul_inv_eq_one.mp
  simpa only [mul_inv_rev,mul_assoc] using hp

variable (hs : Subgroup.closure (s : Set Γ)=⊤)
include hs

lemma projected_commute_all (g h : Γ) :
    Commute (projectedHalf x s t g) (projectedRight x s t h) :=
  commute_homs_of_generators (s : Set Γ) hs (projectedHalf x s t) (projectedRight x s t)
    (fun _ hg _ hh => projected_commute x s t hg hh) g h

def projectedDiagonal : Γ →* RelationQuotient x s t where
  toFun g := projectedHalf x s t g * projectedRight x s t g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    exact ((projected_commute_all x s t hs h g).symm.mul_mul_mul_comm _ _).symm

lemma projected_fixed {g : MulAction.stabilizer Γ x} (hg : g∈t) :
    projectedRoot x s t g.val=projectedDiagonal x s t hs g.val := by
  have hrel : fixedWord x g∈finiteRelations x s t :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)
  have hp := projection_rel x s t hrel
  change projection x s t (rootWord x g.val * (halfWord x g.val * rightWord x g.val)⁻¹)=1 at hp
  simp only [map_mul,map_inv] at hp
  exact mul_inv_eq_one.mp hp

lemma projected_fixed_all (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
    (g : MulAction.stabilizer Γ x) :
    projectedRoot x s t g.val=projectedDiagonal x s t hs g.val := by
  have he : (projectedRoot x s t).comp (MulAction.stabilizer Γ x).subtype=
      (projectedDiagonal x s t hs).comp (MulAction.stabilizer Γ x).subtype := by
    apply MonoidHom.eq_of_eqOn_dense ht
    intro k hk
    exact projected_fixed x s t hs hk
  exact DFunLike.congr_fun he g

lemma commutingWord_mem_relationKernel (g h : Γ) :
    commutingWord x g h∈relationKernel x s t := by
  apply (QuotientGroup.eq_one_iff _).mp
  change projection x s t (commutingWord x g h)=1
  simp only [commutingWord,map_mul,map_inv]
  change projectedHalf x s t g * projectedRight x s t h * (projectedHalf x s t g)⁻¹ *
    (projectedRight x s t h)⁻¹=1
  rw [(projected_commute_all x s t hs g h).eq]
  group

lemma fixedWord_mem_relationKernel (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤)
    (g : MulAction.stabilizer Γ x) : fixedWord x g∈relationKernel x s t := by
  apply (QuotientGroup.eq_one_iff _).mp
  change projection x s t (fixedWord x g)=1
  simp only [fixedWord,map_mul,map_inv]
  change projectedRoot x s t g.val * (projectedDiagonal x s t hs g.val)⁻¹=1
  rw [projected_fixed_all x s t hs ht]
  exact mul_inv_cancel _

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

/-- The two universal label families. Other finite-table relations are not
included here: in particular this is not asserted to be the evaluation kernel. -/
def labelRelations : Set (Seed (Γ:=Γ) x) :=
  Set.range (fun gh : Γ × Γ => commutingWord x gh.1 gh.2) ∪
  Set.range (fixedWord (Γ:=Γ) x)

lemma labelRelations_mem_ker : labelRelations (Γ:=Γ) x ⊆
    ((evaluation (Γ:=Γ) x).ker : Set (Seed (Γ:=Γ) x)) := by
  rintro r (⟨⟨g,h⟩,rfl⟩|⟨g,rfl⟩)
  · exact evaluation_commutingWord x g h
  · exact evaluation_fixedWord x g

lemma finiteRelations_subset_labelRelations (s : Finset Γ)
    (t : Finset (MulAction.stabilizer Γ x)) :
    (finiteRelations x s t : Set (Seed (Γ:=Γ) x)) ⊆ labelRelations x := by
  intro r hr
  simp only [finiteRelations,Finset.mem_coe,Finset.mem_union,Finset.mem_image] at hr
  rcases hr with ⟨⟨g,h⟩,_,rfl⟩|⟨g,_,rfl⟩
  · exact Or.inl ⟨(g,h),rfl⟩
  · exact Or.inr ⟨g,rfl⟩

/-- All the infinitely many disjoint half-copy commutators and point-stabilizer
splitting relations follow from their values on finite generating sets. -/
lemma labelRelations_normalClosure (s : Finset Γ)
    (t : Finset (MulAction.stabilizer Γ x))
    (hs : Subgroup.closure (s : Set Γ)=⊤)
    (ht : Subgroup.closure (t : Set (MulAction.stabilizer Γ x))=⊤) :
    Subgroup.normalClosure (labelRelations x)=relationKernel x s t := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro r (⟨⟨g,h⟩,rfl⟩|⟨g,rfl⟩)
    · exact commutingWord_mem_relationKernel x s t hs g h
    · exact fixedWord_mem_relationKernel x s t hs ht g
  · exact Subgroup.normalClosure_mono (finiteRelations_subset_labelRelations x s t)

lemma labelRelations_finitelyNormallyGenerated [Group.FG Γ]
    [Group.FG (MulAction.stabilizer Γ x)] :
    (Subgroup.normalClosure (labelRelations (Γ:=Γ) x)).IsFinitelyNormallyGenerated := by
  obtain ⟨s,hs⟩ := Group.fg_def.mp (inferInstance : Group.FG Γ)
  obtain ⟨t,ht⟩ := Group.fg_def.mp (inferInstance : Group.FG (MulAction.stabilizer Γ x))
  refine ⟨(finiteRelations x s t : Set (Seed (Γ:=Γ) x)),(finiteRelations x s t).finite_toSet,?_⟩
  exact (labelRelations_normalClosure x s t hs ht).symm

/-- A genuine finitely presented intermediate quotient. The still-missing
relations cannot be discarded: this quotient is not identified with the
finite-table group. -/
abbrev LabelQuotient := Seed (Γ:=Γ) x ⧸ Subgroup.normalClosure (labelRelations (Γ:=Γ) x)

instance labelQuotient_finitelyPresented [Group.IsFinitelyPresented Γ]
    [Group.FG Γ] [Group.FG (MulAction.stabilizer Γ x)] :
    Group.IsFinitelyPresented (LabelQuotient (Γ:=Γ) x) :=
  Group.IsFinitelyPresented.quotient _ (labelRelations_finitelyNormallyGenerated x)

def labelEvaluation : LabelQuotient (Γ:=Γ) x →* group (Γ:=Γ) (X:=X) :=
  QuotientGroup.lift _ (evaluation (Γ:=Γ) x)
    (Subgroup.normalClosure_le_normal (labelRelations_mem_ker x))

lemma labelEvaluation_surjective [MulAction.IsPretransitive Γ X] :
    Function.Surjective (labelEvaluation (Γ:=Γ) x) := by
  intro g
  obtain ⟨w,hw⟩ := evaluation_surjective x g
  exact ⟨QuotientGroup.mk w,hw⟩

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

/-- Detect the missing untwisted relators by an actual abelian quotient of the
partially presented group. This is a diagnostic, not the desired endpoint. -/
def untwistedSum : Seed (Γ:=Γ) x →* Multiplicative ℤ :=
  Monoid.Coprod.lift (Monoid.Coprod.lift 1 1)
    (FreeGroup.lift (fun _ : finiteSet (Γ:=Γ) x => Multiplicative.ofAdd (1:ℤ)))

@[simp] lemma untwistedSum_root (g : Γ) : untwistedSum x (rootWord x g)=1 := by rfl
@[simp] lemma untwistedSum_half (g : Γ) : untwistedSum x (halfWord x g)=1 := by rfl
@[simp] lemma untwistedSum_flip :
    untwistedSum (Γ:=Γ) x (flipWord (Γ:=Γ) x)=Multiplicative.ofAdd (1:ℤ) := by rfl
@[simp] lemma untwistedSum_right (g : Γ) : untwistedSum x (rightWord x g)=1 := by
  change untwistedSum x (flipWord x * halfWord x g * (flipWord x)⁻¹)=1
  simp only [map_mul,map_inv,untwistedSum_half,mul_one,mul_inv_cancel]

lemma labelRelations_mem_untwistedSum_ker : labelRelations (Γ:=Γ) x ⊆
    ((untwistedSum (Γ:=Γ) x).ker : Set (Seed (Γ:=Γ) x)) := by
  rintro r (⟨⟨g,h⟩,rfl⟩|⟨g,rfl⟩)
  · change untwistedSum x (commutingWord x g h)=1
    simp [commutingWord]
  · change untwistedSum x (fixedWord x g)=1
    simp [fixedWord]

lemma flip_mul_self : flip (Γ:=Γ) x * flip x=1 := by
  change (Partition.bit x).permute (Γ:=Γ) Equiv.boolNot *
    (Partition.bit x).permute Equiv.boolNot=1
  rw [← map_mul]
  have h : (Equiv.boolNot : Equiv.Perm Bool) * Equiv.boolNot=1 := by
    ext b
    cases b <;> rfl
  rw [h,map_one]

/-- An explicit genuine table relation that is NOT a consequence of the two
finite label families, even after using every acting-group and stabilizer element. -/
theorem labelRelations_strictly_incomplete :
    (flipWord (Γ:=Γ) x)^2∈(evaluation (Γ:=Γ) x).ker ∧
      (flipWord (Γ:=Γ) x)^2∉Subgroup.normalClosure (labelRelations (Γ:=Γ) x) := by
  constructor
  · change evaluation (Γ:=Γ) x ((flipWord x)^2)=1
    rw [map_pow,evaluation_flipWord,pow_two,flip_mul_self]
  · intro h
    have hh := Subgroup.normalClosure_le_normal (labelRelations_mem_untwistedSum_ker x) h
    change untwistedSum (Γ:=Γ) x ((flipWord x)^2)=1 at hh
    rw [map_pow,untwistedSum_flip] at hh
    have : (2:ℤ)=0 := congrArg Multiplicative.toAdd hh
    norm_num at this

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes
namespace FiniteLocalizationClosure
universe u v
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Group K]
variable (f : K →* K) (a : K) (s r : Finset K)

/-- The discrepancy between twice-localizing and conjugating a localization. -/
def discrepancy (g : K) : K := f (f g) * (a * f g * a⁻¹)⁻¹

def baseRelations : Finset K := r ∪ s.image (discrepancy f a)
def relations : Finset K := baseRelations f a s r ∪ (baseRelations f a s r).image f

def kernel : Subgroup K := Subgroup.normalClosure (relations f a s r : Set K)
instance : (kernel f a s r).Normal := Subgroup.normalClosure_normal
abbrev Quotient := K ⧸ kernel f a s r

def project : K →* Quotient f a s r := QuotientGroup.mk' _

lemma project_base {g : K} (hg : g∈baseRelations f a s r) : project f a s r g=1 :=
  (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Finset.mem_union_left _ hg))

lemma project_local_base {g : K} (hg : g∈baseRelations f a s r) : project f a s r (f g)=1 :=
  (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)))

variable (hs : Subgroup.closure (s : Set K)=⊤)
include hs

lemma twice_eq_conjugate (g : K) :
    project f a s r (f (f g))=project f a s r (a * f g * a⁻¹) := by
  have he : (project f a s r).comp (f.comp f)=
      (project f a s r).comp ((MulAut.conj a).toMonoidHom.comp f) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro k hk
    have h := project_base f a s r (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,hk,rfl⟩))
    change project f a s r (f (f k) * (a*f k*a⁻¹)⁻¹)=1 at h
    rw [map_mul,map_inv] at h
    exact mul_inv_eq_one.mp h
  exact DFunLike.congr_fun he g

/-- Adding a finite set of relations, their first localizations, and the finite
self-similarity checks suffices to make the entire normal closure stable under f.
No infinitely iterated family is silently assumed finite. -/
lemma kernel_stable : kernel f a s r ≤ (kernel f a s r).comap f := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact Subgroup.subset_normalClosure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩))
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hg
    change f (f k)∈kernel f a s r
    apply (QuotientGroup.eq_one_iff _).mp
    change project f a s r (f (f k))=1
    rw [twice_eq_conjugate f a s r hs,map_mul,map_mul,map_inv,project_local_base f a s r hk]
    simp

def localization : Quotient f a s r →* Quotient f a s r :=
  QuotientGroup.map _ _ f (kernel_stable f a s r hs)

lemma localization_project (g : K) :
    localization f a s r hs (project f a s r g)=project f a s r (f g) := rfl

lemma localizations_in_kernel {g : K} (hg : g∈kernel f a s r) (n : ℕ) :
    (f^[n]) g∈kernel f a s r := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact kernel_stable f a s r hs ih

omit hs in
lemma kernel_finitelyNormallyGenerated : (kernel f a s r).IsFinitelyNormallyGenerated :=
  ⟨(relations f a s r : Set K),(relations f a s r).finite_toSet,rfl⟩

omit hs in
instance quotient_finitelyPresented [Group.IsFinitelyPresented K] :
    Group.IsFinitelyPresented (Quotient f a s r) :=
  Group.IsFinitelyPresented.quotient _ (kernel_finitelyNormallyGenerated f a s r)

variable {H : Type v} [Group H]
variable (e : K →* H) (l : H →* H)
variable (he : ∀ g,e (f g)=l (e g))
variable (hl : ∀ h,l (l h)=e a*l h*(e a)⁻¹)
variable (hr : ∀ g∈r,e g=1)
include he hl hr

omit hs in
lemma relations_valid : (relations f a s r : Set K) ⊆ (e.ker : Set K) := by
  have hb : ∀ g∈baseRelations f a s r,e g=1 := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg|hg
    · exact hr g hg
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hg
      change e (f (f k) * (a*f k*a⁻¹)⁻¹)=1
      simp only [map_mul,map_inv,he,hl,mul_inv_cancel]
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact hb g hg
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hg
    change e (f k)=1
    rw [he,hb k hk,map_one]

omit hs in
def evaluate : Quotient f a s r →* H :=
  QuotientGroup.lift _ e (Subgroup.normalClosure_le_normal (relations_valid f a s r e l he hl hr))

omit hs in
lemma evaluate_surjective (he_surj : Function.Surjective e) :
    Function.Surjective (evaluate f a s r e l he hl hr) := by
  intro h
  obtain ⟨g,hg⟩ := he_surj h
  exact ⟨QuotientGroup.mk g,hg⟩

end FiniteLocalizationClosure
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X)

def generatorWord (g : finiteSet (Γ:=Γ) x) : Seed (Γ:=Γ) x :=
  Monoid.Coprod.inr (FreeGroup.of g)

@[simp] lemma evaluation_generatorWord (g : finiteSet (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (generatorWord x g)=g.val := by rfl

def associatorWord : Seed (Γ:=Γ) x :=
  generatorWord x ⟨associator x,by simp [finiteSet]⟩

@[simp] lemma evaluation_associatorWord :
    evaluation (Γ:=Γ) x (associatorWord (Γ:=Γ) x)=associator x := by rfl

lemma localize_twice (g : group (Γ:=Γ) (X:=X)) :
    localize (left x) (localize (left x) g)=
      associator x * localize (left x) g * (associator x)⁻¹ := by
  rw [← localize_comp]
  exact (localize_conj (associator x) (associator_left x) g).symm

variable [MulAction.IsPretransitive Γ X]

/-- An actual lift of prefix localization to the presentation seed. It respects
both Γ factors as homomorphisms; only the free factor uses chosen preimages. -/
def localizationSeed : Seed (Γ:=Γ) x →* Seed (Γ:=Γ) x :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift (halfWord x)
      ((MulAut.conj (associatorWord x)).toMonoidHom.comp (halfWord x)))
    (FreeGroup.lift (fun g : finiteSet (Γ:=Γ) x =>
      (evaluation_surjective (Γ:=Γ) x (localize (left x) g.val)).choose))

lemma localizationSeed_correct :
    (evaluation (Γ:=Γ) x).comp (localizationSeed x)=
      (localize (left x)).comp (evaluation (Γ:=Γ) x) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.Coprod.hom_ext
    · apply MonoidHom.ext
      intro g
      rfl
    · apply MonoidHom.ext
      intro g
      change evaluation (Γ:=Γ) x (associatorWord x * halfWord x g * (associatorWord x)⁻¹)=
        localize (left x) (localize (left x) (embedding g))
      rw [map_mul,map_mul,map_inv,evaluation_associatorWord,evaluation_halfWord]
      exact (localize_twice x (embedding g)).symm
  · apply FreeGroup.ext_hom
    intro g
    change evaluation (Γ:=Γ) x
      (FreeGroup.lift (fun k : finiteSet (Γ:=Γ) x =>
        (evaluation_surjective (Γ:=Γ) x (localize (left x) k.val)).choose) (FreeGroup.of g)) =
      localize (left x) (FreeGroup.lift (fun k : finiteSet (Γ:=Γ) x => k.val) (FreeGroup.of g))
    simpa only [FreeGroup.lift_apply_of] using
      (evaluation_surjective (Γ:=Γ) x (localize (left x) g.val)).choose_spec

lemma evaluation_localizationSeed (g : Seed (Γ:=Γ) x) :
    evaluation (Γ:=Γ) x (localizationSeed x g)=localize (left x) (evaluation (Γ:=Γ) x g) :=
  DFunLike.congr_fun (localizationSeed_correct x) g

/-- The finite self-similar closure of any given finite family of actual table
relations. Completeness of a particular family still has to be proved. -/
abbrev LocalQuotient (s r : Finset (Seed (Γ:=Γ) x)) :=
  FiniteLocalizationClosure.Quotient (localizationSeed x) (associatorWord x) s r

instance localQuotient_finitelyPresented [Group.IsFinitelyPresented Γ]
    (s r : Finset (Seed (Γ:=Γ) x)) :
    Group.IsFinitelyPresented (LocalQuotient x s r) := inferInstance

def localEvaluation (s r : Finset (Seed (Γ:=Γ) x))
    (hr : ∀ g∈r,evaluation (Γ:=Γ) x g=1) :
    LocalQuotient x s r →* group (Γ:=Γ) (X:=X) :=
  FiniteLocalizationClosure.evaluate _ _ s r (evaluation (Γ:=Γ) x) (localize (left x))
    (evaluation_localizationSeed x)
    (by intro g; rw [evaluation_associatorWord]; exact localize_twice x g) hr

lemma localEvaluation_surjective (s r : Finset (Seed (Γ:=Γ) x))
    (hr : ∀ g∈r,evaluation (Γ:=Γ) x g=1) :
    Function.Surjective (localEvaluation x s r hr) :=
  FiniteLocalizationClosure.evaluate_surjective _ _ s r _ _ _ _ hr (evaluation_surjective x)

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
