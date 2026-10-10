import Mathlib

namespace OAI

/-!
# Blocks, defect groups, and the bounded-order formulation of Donovan's conjecture

This file develops supporting results, not a proof of Donovan's conjecture.
The algebra of a block is the actual corner `b (KG) b = (KG) b`, with identity `b`.
Morita equivalence is Mathlib's equivalence of module categories by a linear functor.

We prove finiteness of blocks for a fixed finite-dimensional algebra, existence of
defect groups, the conditional reduction from bounded-order to fixed-defect Morita
finiteness, and equality of defect subgroups for blocks corresponding under a
coefficient-field embedding.

Uniform bounded-defect-order Morita finiteness across varying finite groups remains
unproved. Block-idempotent descent and bijectivity, preservation of primitivity, and
scalar extension of Morita equivalences are also not established here.
-/
noncomputable section

universe u v w

namespace Donovan

section Blocks

variable {A : Type u} [Ring A]

/-- A block is a nonzero primitive idempotent in the center, not necessarily
a primitive idempotent of the whole ring. -/
def IsBlockIdempotent (b : A) : Prop :=
  b ≠ 0 ∧ IsIdempotentElem b ∧ IsMulCentral b ∧
    ∀ e : A, IsIdempotentElem e → IsMulCentral e → e * b = e → e = 0 ∨ e = b

/-- The block idempotents in a ring. -/
def BlockIdempotent (A : Type u) [Ring A] := {b : A // IsBlockIdempotent b}

namespace BlockIdempotent

instance : Coe (BlockIdempotent A) A := ⟨Subtype.val⟩

@[ext] theorem ext {b c : BlockIdempotent A} (h : (b : A) = c) : b = c :=
  Subtype.ext h

theorem ne_zero (b : BlockIdempotent A) : (b : A) ≠ 0 := b.property.1

theorem idempotent (b : BlockIdempotent A) : IsIdempotentElem (b : A) :=
  b.property.2.1

theorem central (b : BlockIdempotent A) : IsMulCentral (b : A) :=
  b.property.2.2.1

theorem primitive (b : BlockIdempotent A) (e : A)
    (he : IsIdempotentElem e) (hc : IsMulCentral e) (heb : e * b = e) :
    e = 0 ∨ e = b :=
  b.property.2.2.2 e he hc heb

/-- The ring of the block: the corner has identity `b`, rather than the
identity of the ambient ring. -/
abbrev Algebra (b : BlockIdempotent A) := b.idempotent.Corner

/-- For a central idempotent the corner is exactly the summand `A b`. -/
theorem mem_corner_iff (b : BlockIdempotent A) (x : A) :
    x ∈ Subsemigroup.corner (b : A) ↔ ∃ a : A, a * b = x :=
  Subsemigroup.mem_corner_iff_mem_range_mul_right b.idempotent b.central

variable (K : Type v) [CommRing K] [_root_.Algebra K A]

/-- Scalars in the block are `k b`. In particular the identity is `b`. -/
def scalarHom (b : BlockIdempotent A) : K →+* b.Algebra where
  toFun k := ⟨k • (b : A), by
    rw [Subsemigroup.mem_corner_iff b.idempotent]
    constructor
    · rw [mul_smul_comm, b.idempotent.eq]
    · rw [smul_mul_assoc, b.idempotent.eq]⟩
  map_zero' := Subtype.ext (zero_smul K (b : A))
  map_one' := Subtype.ext (one_smul K (b : A))
  map_add' k l := Subtype.ext (add_smul k l (b : A))
  map_mul' k l := Subtype.ext (by
    change (k * l) • (b : A) = (k • (b : A)) * (l • (b : A))
    rw [smul_mul_smul_comm, b.idempotent.eq])

instance algebra (b : BlockIdempotent A) : _root_.Algebra K b.Algebra :=
  (scalarHom K b).toAlgebra' fun k x => Subtype.ext (by
    change (k • (b : A)) * (x.val : A) = (x.val : A) * (k • (b : A))
    rw [smul_mul_assoc, mul_smul_comm,
      ((Subsemigroup.mem_corner_iff b.idempotent).mp x.property).1,
      ((Subsemigroup.mem_corner_iff b.idempotent).mp x.property).2])

/-- Inclusion of the block into the ambient algebra is linear. It is not
generally a unital homomorphism of rings, since the identities differ. -/
def inclusion (b : BlockIdempotent A) : b.Algebra →ₗ[K] A where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' k x := by
    change (k • (b : A)) * x.val = k • x.val
    rw [smul_mul_assoc, ((Subsemigroup.mem_corner_iff b.idempotent).mp x.property).1]

theorem inclusion_injective (b : BlockIdempotent A) :
    Function.Injective (inclusion K b) := Subtype.val_injective

end BlockIdempotent
end Blocks

section FinitelyManyBlocksOfOneAlgebra

variable {A : Type u} [Ring A]

namespace BlockIdempotent

/-- Distinct primitive central idempotents are orthogonal. -/
theorem mul_eq_zero {b c : BlockIdempotent A} (h : b ≠ c) : (b : A) * c = 0 := by
  have he : IsIdempotentElem ((b : A) * c) := by
    change ((b : A) * c) * ((b : A) * c) = (b : A) * c
    calc
      ((b : A) * c) * ((b : A) * c) = (b : A) * ((c : A) * b) * c :=
        by simp only [mul_assoc]
      _ = (b : A) * ((b : A) * c) * c := by rw [(c.central.comm (b : A)).eq]
      _ = ((b : A) * b) * ((c : A) * c) := by simp only [mul_assoc]
      _ = (b : A) * c := by rw [b.idempotent.eq, c.idempotent.eq]
  have hc : IsMulCentral ((b : A) * c) := Set.mul_mem_center b.central c.central
  have hb : ((b : A) * c) * b = (b : A) * c := by
    rw [mul_assoc, (c.central.comm (b : A)).eq, ← mul_assoc, b.idempotent.eq]
  have hc' : ((b : A) * c) * c = (b : A) * c := by
    rw [mul_assoc, c.idempotent.eq]
  obtain hz | hb' := b.primitive _ he hc hb
  · exact hz
  obtain hz | hc'' := c.primitive _ he hc hc'
  · exact hz
  exact (h (ext (hb'.symm.trans hc''))).elim

variable (K : Type v) [Field K] [_root_.Algebra K A]

/-- Primitive central idempotents form a linearly independent family. -/
theorem linearIndependent : LinearIndependent K (fun b : BlockIdempotent A => (b : A)) := by
  classical
  rw [linearIndependent_iff']
  intro s f hs i hi
  have h := congrArg (fun x : A => x * (i : A)) hs
  rw [Finset.sum_mul, zero_mul, Finset.sum_eq_single_of_mem i hi] at h
  · rw [smul_mul_assoc, i.idempotent.eq] at h
    exact (smul_eq_zero.mp h).resolve_right i.ne_zero
  · intro j _ hji
    rw [smul_mul_assoc, mul_eq_zero hji, smul_zero]

/-- A single finite-dimensional algebra has only finitely many blocks.
This does not bound the number of Morita types as the algebra varies. -/
theorem finite [Module.Finite K A] : Finite (BlockIdempotent A) :=
  (linearIndependent (A := A) K).finite

/-- A block of a finite-dimensional algebra is itself finite-dimensional,
for its natural scalar structure. -/
theorem finiteDimensional_corner [Module.Finite K A] (b : BlockIdempotent A) :
    FiniteDimensional K b.Algebra :=
  FiniteDimensional.of_injective (inclusion K b) (inclusion_injective K b)

end BlockIdempotent
end FinitelyManyBlocksOfOneAlgebra

section DefectGroups

variable {K : Type v} [Field K] {G : Type u} [Group G]

/-- A block idempotent is fixed under conjugation by every group element.
Thus it belongs to the domain of each genuine Brauer map. -/
theorem BlockIdempotent.conjugation_fixed (b : BlockIdempotent (MonoidAlgebra K G))
    (g : G) :
    MonoidAlgebra.single g 1 * (b : MonoidAlgebra K G) *
      MonoidAlgebra.single g⁻¹ 1 = (b : MonoidAlgebra K G) := by
  rw [← (b.central.comm (MonoidAlgebra.single g 1)).eq, mul_assoc,
    MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
    ← MonoidAlgebra.one_def, mul_one]

/-- Delete coefficients outside the centralizer of `D`. On the `D`-fixed group algebra
in characteristic `p`, for a `p`-subgroup `D`, this is the Brauer map. We only use it on
central idempotents; no multiplicativity on the entire group algebra is asserted. -/
def brauerProjection (D : Subgroup G) (x : MonoidAlgebra K G) :
    MonoidAlgebra K (Subgroup.centralizer (D : Set G)) :=
  MonoidAlgebra.ofCoeff (x.coeff.subtypeDomain
    (fun g => g ∈ Subgroup.centralizer (D : Set G)))

@[simp] theorem brauerProjection_coeff (D : Subgroup G) (x : MonoidAlgebra K G)
    (g : Subgroup.centralizer (D : Set G)) :
    (brauerProjection D x).coeff g = x.coeff g.val := rfl

@[simp] theorem brauerProjection_zero (D : Subgroup G) :
    brauerProjection D (0 : MonoidAlgebra K G) = 0 := rfl

/-- Defect groups are maximal, under inclusion, among the `p`-subgroups
with nonzero Brauer image. This does not impose a commutativity condition. -/
def IsDefectGroup (p : ℕ) (b : BlockIdempotent (MonoidAlgebra K G))
    (D : Subgroup G) : Prop :=
  Maximal (fun Q : Subgroup G => IsPGroup p Q ∧ brauerProjection Q (b : MonoidAlgebra K G) ≠ 0) D

@[simp] theorem brauerProjection_bot_eq_zero_iff (x : MonoidAlgebra K G) :
    brauerProjection (⊥ : Subgroup G) x = 0 ↔ x = 0 := by
  change MonoidAlgebra.ofCoeff _ = 0 ↔ x = 0
  rw [MonoidAlgebra.ofCoeff_eq_zero, Finsupp.subtypeDomain_eq_zero_iff]
  · exact MonoidAlgebra.coeff_eq_zero
  · intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : h = 1 := Subgroup.mem_bot.mp hh
    simp [this]

/-- Any `p`-subgroup with nonzero Brauer image is contained in a defect
group. This uses finiteness of the subgroup poset. -/
theorem exists_defectGroup_ge [Finite G] (p : ℕ)
    (b : BlockIdempotent (MonoidAlgebra K G)) (Q : Subgroup G)
    (hQ : IsPGroup p Q) (hbQ : brauerProjection Q (b : MonoidAlgebra K G) ≠ 0) :
    ∃ D : Subgroup G, Q ≤ D ∧ IsDefectGroup p b D :=
  ({D : Subgroup G | IsPGroup p D ∧
    brauerProjection D (b : MonoidAlgebra K G) ≠ 0}).toFinite.exists_le_maximal ⟨hQ, hbQ⟩

/-- A finite-group block has at least one defect group as defined above. -/
theorem exists_defectGroup [Finite G] (p : ℕ)
    (b : BlockIdempotent (MonoidAlgebra K G)) :
    ∃ D : Subgroup G, IsDefectGroup p b D := by
  let s : Set (Subgroup G) :=
    {D | IsPGroup p D ∧ brauerProjection D (b : MonoidAlgebra K G) ≠ 0}
  have hs : s.Nonempty := by
    refine ⟨⊥, IsPGroup.of_bot, ?_⟩
    exact mt (brauerProjection_bot_eq_zero_iff (b : MonoidAlgebra K G)).mp b.ne_zero
  exact s.toFinite.exists_maximal hs

end DefectGroups

section MoritaClasses

/-- A block of a finite group algebra over `K`. The group is allowed to
vary over all finite group types in the specified universe. -/
structure FiniteGroupBlock (K : Type v) [Field K] where
  G : Type u
  [group : Group G]
  [finite : Finite G]
  block : BlockIdempotent (MonoidAlgebra K G)

attribute [instance] FiniteGroupBlock.group FiniteGroupBlock.finite

namespace FiniteGroupBlock

variable {K : Type v} [Field K]

/-- The actual block algebra `KGb`. -/
abbrev Algebra (B : FiniteGroupBlock.{u, v} K) := B.block.Algebra

/-- The equivalence relation is linear Morita equivalence, not ring
isomorphism or equivalence of the underlying un-enriched categories. -/
def moritaSetoid (K : Type v) [Field K] : Setoid (FiniteGroupBlock.{u, v} K) where
  r B C := IsMoritaEquivalent K B.Algebra C.Algebra
  iseqv := ⟨fun B => IsMoritaEquivalent.refl K B.Algebra,
    fun h => IsMoritaEquivalent.symm K h, fun h h' => IsMoritaEquivalent.trans K h h'⟩

end FiniteGroupBlock

/-- Morita classes of all finite-group blocks over the fixed field `K`. -/
def MoritaClass (K : Type v) [Field K] :=
  Quotient (FiniteGroupBlock.moritaSetoid.{u, v} K)

/-- The Morita class represented by a block. -/
def moritaClass {K : Type v} [Field K] (B : FiniteGroupBlock.{u, v} K) :
    MoritaClass.{u, v} K := Quotient.mk _ B

/-- The block has a defect group whose order is at most `M`. -/
def HasDefectAtMost {K : Type v} [Field K] (p M : ℕ) (B : FiniteGroupBlock.{u, v} K) :
    Prop :=
  ∃ D : Subgroup B.G, IsDefectGroup p B.block D ∧ Nat.card D ≤ M

/-- The block has a defect group isomorphic to the given group `P`. -/
def HasDefectIsomorphic {K : Type v} [Field K] (p : ℕ) (P : Type w) [Group P]
    (B : FiniteGroupBlock.{u, v} K) : Prop :=
  ∃ D : Subgroup B.G, IsDefectGroup p B.block D ∧ Nonempty (D ≃* P)

/-- Morita classes represented by blocks with a defect group of order at most `M`. -/
def boundedClasses (p : ℕ) (K : Type v) [Field K] (M : ℕ) :
    Set (MoritaClass.{u, v} K) :=
  moritaClass '' {B | HasDefectAtMost p M B}

/-- Morita classes represented by blocks with a defect group isomorphic to `P`. -/
def fixedDefectClasses (p : ℕ) (K : Type v) [Field K] (P : Type w) [Group P] :
    Set (MoritaClass.{u, v} K) :=
  moritaClass '' {B | HasDefectIsomorphic p P B}

variable {p : ℕ} {K : Type v} [Field K]

/-- Equality of classes means linear Morita equivalence of the actual block algebras. -/
theorem moritaClass_eq_iff (B C : FiniteGroupBlock.{u, v} K) :
    moritaClass B = moritaClass C ↔ IsMoritaEquivalent K B.Algebra C.Algebra :=
  Quotient.eq

/-- The order of a defect group is positive. -/
theorem HasDefectAtMost.pos {M : ℕ} {B : FiniteGroupBlock.{u, v} K}
    (h : HasDefectAtMost p M B) : 0 < M := by
  obtain ⟨D, _, hD⟩ := h
  exact lt_of_lt_of_le (Nat.card_pos (α := D)) hD

/-- Every block is covered by some positive bound; the bounded-order classes
are not made empty by the definition of a defect group. -/
theorem exists_positive_defect_bound (p : ℕ) (B : FiniteGroupBlock.{u, v} K) :
    ∃ M : ℕ, 0 < M ∧ HasDefectAtMost p M B := by
  obtain ⟨D, hD⟩ := exists_defectGroup p B.block
  exact ⟨Nat.card D, Nat.card_pos, D, hD, le_rfl⟩

/-- An isomorphism of defect groups gives equality of their orders. -/
theorem HasDefectIsomorphic.hasDefectAtMost {P : Type w} [Group P]
    {B : FiniteGroupBlock.{u, v} K} (h : HasDefectIsomorphic p P B) :
    HasDefectAtMost p (Nat.card P) B := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h
  exact ⟨D, hD, (Nat.card_congr e.toEquiv).le⟩

/-- The fixed-defect classes are a subset of the bounded-order classes. -/
theorem fixedDefectClasses_subset (p : ℕ) (K : Type v) [Field K]
    (P : Type w) [Group P] :
    fixedDefectClasses.{u, v, w} p K P ⊆ boundedClasses p K (Nat.card P) := by
  rintro _ ⟨B, hB, rfl⟩
  exact ⟨B, hB.hasDefectAtMost, rfl⟩

/-- The elementary fixed-defect reduction. Uniform bounded-order finiteness is
an assumption, not a result proved here. There is no abelian hypothesis on `P`. -/
theorem finite_fixedDefectClasses_of_bounded
    (h : ∀ M : ℕ, 0 < M → (boundedClasses.{u, v} p K M).Finite)
    (P : Type w) [Group P] [Finite P] :
    (fixedDefectClasses.{u, v, w} p K P).Finite :=
  (h (Nat.card P) Nat.card_pos).subset (fixedDefectClasses_subset p K P)

namespace FiniteGroupBlock

variable {G : Type u} [Group G] [Finite G]

/-- Regard a block for one fixed ambient group as a member of the class of
all finite-group blocks. -/
def ofBlock (b : BlockIdempotent (MonoidAlgebra K G)) : FiniteGroupBlock.{u, v} K where
  G := G
  block := b

end FiniteGroupBlock

/-- For a fixed finite group, its blocks give a finite collection of Morita
classes. This is only the fixed-ambient-group claim, not Donovan's theorem. -/
theorem finite_classes_for_one_group (K : Type v) [Field K]
    (G : Type u) [Group G] [Finite G] :
    (Set.range (fun b : BlockIdempotent (MonoidAlgebra K G) =>
      moritaClass (FiniteGroupBlock.ofBlock b))).Finite := by
  have : Finite (BlockIdempotent (MonoidAlgebra K G)) := BlockIdempotent.finite K
  exact Set.finite_range _

end MoritaClasses

section CoefficientExtension

variable {K : Type v} [Field K] {L : Type w} [Field L]
variable {G : Type u} [Group G]

/-- Applying a field embedding to group-ring coefficients is injective. -/
theorem coefficientExtension_injective (f : K →+* L) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro x y h
  apply MonoidAlgebra.ext
  ext g
  apply f.injective
  simpa only [MonoidAlgebra.coeff_mapRingHom] using
    congrArg (fun z : MonoidAlgebra L G => z.coeff g) h

/-- Deleting coefficients outside the centralizer commutes with applying a
field embedding. This is the coefficient calculation for the Brauer map. -/
theorem brauerProjection_coefficientExtension (f : K →+* L) (D : Subgroup G)
    (x : MonoidAlgebra K G) :
    brauerProjection D (MonoidAlgebra.mapRingHom G f x) =
      MonoidAlgebra.mapRingHom (Subgroup.centralizer (D : Set G)) f
        (brauerProjection D x) := by
  apply MonoidAlgebra.ext
  ext g
  simp only [brauerProjection_coeff, MonoidAlgebra.coeff_mapRingHom]

/-- The vanishing criterion used to compute defects is unchanged by a
coefficient-field embedding. -/
theorem brauerProjection_coefficientExtension_eq_zero_iff (f : K →+* L)
    (D : Subgroup G) (x : MonoidAlgebra K G) :
    brauerProjection D (MonoidAlgebra.mapRingHom G f x) = 0 ↔
      brauerProjection D x = 0 := by
  rw [brauerProjection_coefficientExtension]
  constructor
  · intro h
    apply coefficientExtension_injective f
    simpa only [map_zero] using h
  · intro h
    simp only [h, map_zero]

/-- If two actual block idempotents correspond by coefficient extension,
then their defect subgroups are identical. This lemma does not assert
that every block descends, or that primitivity is preserved. -/
theorem isDefectGroup_coefficientExtension_iff (f : K →+* L) (p : ℕ)
    (b : BlockIdempotent (MonoidAlgebra K G))
    (c : BlockIdempotent (MonoidAlgebra L G))
    (h : MonoidAlgebra.mapRingHom G f (b : MonoidAlgebra K G) = (c : MonoidAlgebra L G))
    (D : Subgroup G) : IsDefectGroup p c D ↔ IsDefectGroup p b D := by
  unfold IsDefectGroup Maximal
  simp only [← h, ne_eq, brauerProjection_coefficientExtension_eq_zero_iff]

end CoefficientExtension

end Donovan

end

end OAI
