import Mathlib
import OAI.Computability.MaxCut.Games.OrientedBlockKernel

namespace OAI

noncomputable section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

namespace MaxCutGames.Quadratic

section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem dot_add_first_inline_BlockRestriction (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

/-- The actual trace character as a binary linear functional. -/
def blockCharacterLinear (g z : Vec F) :
    (Vec F × Vec F) →ₗ[ZMod 2] ZMod 2 where
  toFun := blockCharacter g z
  map_add' := by
    intro p q
    simp only [blockCharacter, Prod.fst_add, Prod.snd_add, dot_add_right, map_add]
    ring
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> simp [blockCharacter]

/-- Restriction to one block, linear in the logical character `z`. -/
def blockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) :
    S →ₗ[ZMod 2] ((U v) →ₗ[ZMod 2] ZMod 2) where
  toFun z := (blockCharacterLinear (g z) z).comp (U v).subtype
  map_add' := by
    intro z w
    ext p
    simp only [LinearMap.comp_apply, blockCharacterLinear, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply, map_add, Submodule.coe_add,
      blockCharacter, dot_add_first_inline_BlockRestriction, map_add]
    ring
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext p <;>
      simp [blockCharacterLinear, blockCharacter]

omit [Fintype F] in
@[simp] theorem blockRestriction_apply (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) (p : U v) :
    blockRestriction S g v z p = blockCharacter (g z) z p := rfl

omit [Fintype F] in
/-- Equality to zero is exactly annihilation of the underlying block. -/
theorem blockRestriction_eq_zero_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) :
    blockRestriction S g v z = 0 ↔ BlockAnnihilates (g z) z v := by
  constructor
  · intro h p hp
    exact LinearMap.congr_fun h ⟨p, hp⟩
  · intro h
    ext p
    exact h p p.property

/-- The exact kernel formula for a nonzero logical character. -/
theorem mem_ker_blockRestriction_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) {v : Vec F} (hv : v ≠ 0)
    {z : S} (hz : z ≠ 0) :
    z ∈ (blockRestriction S g v).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  have hz' : (z : Vec F) ≠ 0 := fun h => hz (Subtype.ext h)
  rw [LinearMap.mem_ker, blockRestriction_eq_zero_iff, blockAnnihilates_iff hv hz']

/-- Nonproportionality of a generic space makes every actual block kernel
contain at most one nonzero character. -/
theorem blockRestriction_nonzero_kernel_unique
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S)
    (z w : S) (hz : z ≠ 0) (hw : w ≠ 0)
    (hgz : blockRestriction S g v z = 0)
    (hgw : blockRestriction S g v w = 0) : z = w := by
  have hzline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v z).mp hgz)
  have hwline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v w).mp hgw)
  obtain ⟨t, ht⟩ := (mem_line_iff v z).mp hzline
  obtain ⟨s, hs⟩ := (mem_line_iff v w).mp hwline
  have hsne : s ≠ 0 := by
    intro hzero
    apply hw
    apply Subtype.ext
    simpa [hzero] using hs.symm
  apply hS.1 z w hz hw
  refine ⟨t / s, ?_⟩
  rw [← ht, ← hs, smul_smul, div_mul_cancel₀ _ hsne]

/-- Every actual child restriction map loses at most one binary dimension. -/
theorem finrank_ker_blockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) (blockRestriction S g v).ker ≤ 1 :=
  finrank_ker_le_one_of_nonzero_unique (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

theorem finrank_blockRestriction_source_le_range_add_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) S ≤
      Module.finrank (ZMod 2) (blockRestriction S g v).range + 1 :=
  finrank_source_le_range_add_one (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

end

/-!
# Orientation-independent character kernels

Changing the binary parametrization of a block only pulls its dual back along
a linear equivalence.  This leaves the logical kernel unchanged and places
all child maps in one fixed dual space for the finite counting argument.
-/

variable {F B : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [AddCommGroup B] [Module (ZMod 2) B]

/-- The actual child restriction after a choice of block orientation. -/
def orientedBlockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    S →ₗ[ZMod 2] (B →ₗ[ZMod 2] ZMod 2) :=
  J.dualMap.toLinearMap.comp (blockRestriction S g v)

omit [Fintype F] in
@[simp] theorem orientedBlockRestriction_apply
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) (b : B) :
    orientedBlockRestriction S g v J z b = blockCharacter (g z) z (J b) := rfl

omit [Fintype F] in
theorem orientedBlockRestriction_eq_zero_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) :
    orientedBlockRestriction S g v J z = 0 ↔ blockRestriction S g v z = 0 := by
  change J.dualMap (blockRestriction S g v z) = 0 ↔ _
  constructor
  · intro h
    apply J.dualMap.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

omit [Fintype F] in
/-- The kernel depends on the field line and common-parent lift, not on `J`. -/
theorem ker_orientedBlockRestriction
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker = (blockRestriction S g v).ker := by
  ext z
  simp only [LinearMap.mem_ker, orientedBlockRestriction_eq_zero_iff]

omit [Fintype F] in
theorem ker_orientedBlockRestriction_independent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J J' : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker =
      (orientedBlockRestriction S g v J').ker := by
  rw [ker_orientedBlockRestriction, ker_orientedBlockRestriction]

theorem mem_ker_orientedBlockRestriction_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (J : B ≃ₗ[ZMod 2] U v)
    {z : S} (hz : z ≠ 0) :
    z ∈ (orientedBlockRestriction S g v J).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  rw [ker_orientedBlockRestriction]
  exact mem_ker_blockRestriction_iff S g hv hz

theorem finrank_ker_orientedBlockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) (J : B ≃ₗ[ZMod 2] U v) :
    Module.finrank (ZMod 2) (orientedBlockRestriction S g v J).ker ≤ 1 := by
  rw [ker_orientedBlockRestriction]
  exact finrank_ker_blockRestriction_le_one S g hv hS

end MaxCutGames.Quadratic

namespace MaxCutGames.Gadget.BlockDescent

open Quadratic OrientedBlockKernel

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev BinaryDual := Vec F →ₗ[ZMod 2] ZMod 2

/-- Coordinates of a binary character subspace under the trace pairing. -/
def traceSpace (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Submodule (ZMod 2) (Vec F) := S.map traceDualEquiv.symm.toLinearMap

def traceSpaceEquiv (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    S ≃ₗ[ZMod 2] traceSpace S :=
  Submodule.equivMapOfInjective traceDualEquiv.symm.toLinearMap
    traceDualEquiv.symm.injective S

omit [CharP F 2] in
theorem traceSpace_finrank (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Module.finrank (ZMod 2) (traceSpace S) = Module.finrank (ZMod 2) S :=
  (traceSpaceEquiv S).finrank_eq.symm

omit [CharP F 2] in
@[simp] theorem traceSpaceEquiv_apply_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : S) :
    (traceSpaceEquiv S z).val = traceDualEquiv.symm z.val := rfl

omit [CharP F 2] in
theorem traceSpaceEquiv_symm_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : traceSpace S) :
    ((traceSpaceEquiv S).symm z).val = traceDualEquiv z.val := by
  apply traceDualEquiv.symm.injective
  have h := congrArg Subtype.val ((traceSpaceEquiv S).apply_symm_apply z)
  simpa only [traceSpaceEquiv_apply_val, LinearEquiv.symm_apply_apply] using h

/-- One binary-linear lift on the trace-coordinate domain, obtained from the
single common parent map. It is fixed before the outgoing line/orientation. -/
def traceLift (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : traceSpace S →ₗ[ZMod 2] Vec F :=
  representTraceFamily (γ.comp (traceSpaceEquiv S).symm.toLinearMap)

/-- Equality of actual child maps after a change of logical coordinates. -/
theorem childCharacter_comp_traceSpaceEquiv
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).comp (traceSpaceEquiv S).symm.toLinearMap =
      orientedBlockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1) i.2 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro b
  change γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 +
    ((traceSpaceEquiv S).symm z).val (i.2 b).val.2 =
      traceBinary (dot (traceLift S γ z) (i.2 b).val.1 + dot z.val (i.2 b).val.2)
  rw [map_add]
  rw [show traceBinary (dot (traceLift S γ z) (i.2 b).val.1) =
    γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 from
      representTraceFamily_spec (γ.comp (traceSpaceEquiv S).symm.toLinearMap) z _]
  rw [traceSpaceEquiv_symm_val, traceDualEquiv_apply]

/-- The child logical image is unchanged by the trace-coordinate domain
isomorphism. This is equality of subspaces, not merely equality of ranks. -/
theorem childCharacter_range_eq
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      (orientedBlockRestriction (traceSpace S) (traceLift S γ)
        (lineGenerator i.1) i.2).range := by
  rw [← childCharacter_comp_traceSpaceEquiv]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).symm

/-- Before the orientation is revealed, the un-oriented image is fixed; the
fresh isomorphism acts only by dual pullback on this fixed image. -/
theorem childCharacter_range_eq_dual_pullback
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      ((blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1)).range).map
        i.2.dualMap.toLinearMap := by
  rw [childCharacter_range_eq]
  exact LinearMap.range_comp _ _

/-- The rank is independent of the fresh orientation. -/
theorem childCharacter_rank_independent
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (J J' : BlockOrientation A) :
    Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J'⟩).range := by
  rw [childCharacter_range_eq_dual_pullback, childCharacter_range_eq_dual_pullback]
  rw [J.dualMap.finrank_map_eq, J'.dualMap.finrank_map_eq]

end MaxCutGames.Gadget.BlockDescent

namespace MaxCutGames.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def commonGamma (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) : S →ₗ[k] (X →ₗ[k] k) :=
  Classical.choose (exists_common_child_character J hJ Q s S L)

omit [FiniteDimensional k B] in
omit [Finite B] in
theorem commonGamma_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (z : S) (h : s.Shift) :
    L.family z (Pi.single i (s.embed h)) =
      childCharacter J (commonGamma J hJ Q s S L) i z (s.logical h) :=
  Classical.choose_spec (exists_common_child_character J hJ Q s S L) i z h

noncomputable def childDomain (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) : Submodule k (B →ₗ[k] k) :=
  LinearMap.range (childCharacter J (commonGamma J hJ Q s S L) i)

noncomputable def childLift (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Lift s (childDomain J hJ Q s S L i) :=
  Classical.choose (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i)

noncomputable def childSection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    childDomain J hJ Q s S L i →ₗ[k] S :=
  Classical.choose (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))

omit [FiniteDimensional k B] [Finite B] in
theorem childSection_rightInverse (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) :
    childCharacter J (commonGamma J hJ Q s S L) i
      (childSection J hJ Q s S L i z) = z.val :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).1 z

omit [FiniteDimensional k B] [Finite B] in
theorem childLift_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) (p : s.Input) :
    (childLift J hJ Q s S L i).family z p =
      L.family (childSection J hJ Q s S L i z) (Pi.single i p) :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).2 z p

omit [FiniteDimensional k B] [Finite B] in
theorem child_detection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (n : s.Noise)
    (hdetect : ∃ z, (childLift J hJ Q s S L i).family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 :=
  descendant_detection_implies_parent J hJ Q s S L _ _ i
    (childLift_spec J hJ Q s S L i) n hdetect

omit [Finite B] in
theorem child_rank_le (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Module.finrank k (childDomain J hJ Q s S L i) ≤ Module.finrank k S :=
  LinearMap.finrank_range_le _

/-- Terminal logical rank along the actual recursively sampled path. The
final uniform symbol is ignored by this rank function. -/
noncomputable def leafRank
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    (n : ℕ) → (S : Submodule k (B →ₗ[k] k)) →
    Lift (Stage.iterate J hJ Q n) S → (Stage.iterate J hJ Q n).Noise → ℕ
  | 0, S, _, _ => Module.finrank k S
  | n + 1, S, L, t => leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2

theorem leafRank_le (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) (t : (Stage.iterate J hJ Q n).Noise) :
    leafRank J hJ Q n S L t ≤ Module.finrank k S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih _ _ _).trans (child_rank_le J hJ Q _ S L t.1)

end MaxCutGames.Gadget.Descent

/-!
# At most `3r` actual lossy field lines

The genericity bound applies to the common-parent lift before a line or an
orientation is chosen.  A nonzero kernel character determines exactly one
projective field line, and its actual kernel equation implies alignment.
-/

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Fintype (FieldLine F) := Fintype.ofFinite _
local instance (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

/-- A total projective-line map; the default is irrelevant on nonzero characters. -/
def characterFieldLine (A₀ : FieldLine F) (z : Vec F) : FieldLine F := by
  classical
  exact if hz : z = 0 then A₀ else Projectivization.mk F z hz

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem characterFieldLine_eq_of_mem {A₀ A : FieldLine F} {z : Vec F}
    (hz : z ≠ 0) (hm : z ∈ line (lineGenerator A)) :
    characterFieldLine A₀ z = A := by
  classical
  rw [characterFieldLine, dite_eq_right hz, ← Projectivization.mk_rep A]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact (mem_line_iff (lineGenerator A) z).mp hm

/-- All maps have the same binary dual codomain, despite their different blocks. -/
def fieldLineRestrictions (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    FieldLine F → S →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  fun A => orientedBlockRestriction S g (lineGenerator A) (J A)

/-- The alignment event written with the displayed three-coordinate dot product. -/
theorem alignedCharacters_eq_alignmentEvent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F) :
    alignedCharacters (fun z : S =>
      dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2)) =
      alignmentEvent (fun z : S => (z : Vec F)) g
        (fun z : S => alignmentRightHandSide (z : Vec F)) := by
  classical
  ext z
  simp [alignedCharacters, alignmentEvent, alignmentRightHandSide,
    Fin.sum_univ_three, dot, mul_comm]

/-- The exact line-loss count, valid for every choice of orientations and every
binary-linear lift, including one chosen adaptively from earlier information. -/
theorem card_loss_fieldLineRestrictions_le
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S)
    (A₀ : FieldLine F) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  classical
  apply card_lossIndices_le (fieldLineRestrictions S g J)
    (fun z : S => dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2))
    (fun z : S => characterFieldLine A₀ (z : Vec F)) (Module.finrank (ZMod 2) S)
  · intro A z hz hzero
    have hk := (mem_ker_orientedBlockRestriction_iff S g
      (lineGenerator_ne_zero A) (J A) hz).mp hzero
    refine ⟨hk.2, characterFieldLine_eq_of_mem ?_ hk.1⟩
    exact fun h => hz (Subtype.ext h)
  · rw [alignedCharacters_eq_alignmentEvent]
    exact hS.2 g

/-- The fallback line is only used to totalize the counting map. -/
theorem card_loss_fieldLineRestrictions_le_three_rank
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0)
  exact card_loss_fieldLineRestrictions_le S g J hS A₀

end MaxCutGames.Quadratic

namespace MaxCutGames.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The finite harmonic potential, by its exact rational recurrence. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | r + 1 => harmonic r + (↑(r + 1))⁻¹

@[simp] theorem harmonic_zero : harmonic 0 = 0 := rfl

@[simp] theorem harmonic_succ (r : ℕ) :
    harmonic (r + 1) = harmonic r + (↑(r + 1))⁻¹ := rfl

theorem harmonic_eq_sum (r : ℕ) :
    harmonic r = ∑ i ∈ Finset.range r, (↑(i + 1) : ℚ)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih => simp [harmonic_succ, Finset.sum_range_succ, ih]

/-- Rational expectation under uniform sampling on a finite space. -/
def average (f : Ω → ℚ) : ℚ := Finset.univ.expect f

/-- Probability of a decidable event in the finite experiment. -/
def probability (p : Ω → Prop) [DecidablePred p] : ℚ :=
  average (fun ω => if p ω then 1 else 0)

theorem average_mono {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g :=
  Finset.expect_le_expect fun ω _ => h ω

theorem average_nonneg {f : Ω → ℚ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f :=
  Finset.expect_nonneg fun ω _ => h ω

@[simp] theorem average_const [Nonempty Ω] (c : ℚ) :
    average (fun _ : Ω => c) = c :=
  Finset.expect_const Finset.univ_nonempty c

theorem average_add (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g :=
  Finset.expect_add_distrib _ _ _

theorem average_sub (f g : Ω → ℚ) :
    average (fun ω => f ω - g ω) = average f - average g :=
  Finset.expect_sub_distrib _ _ _

theorem average_mul_left (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f :=
  (Finset.mul_expect _ _ _).symm

theorem probability_nonneg (p : Ω → Prop) [DecidablePred p] :
    0 ≤ probability p := by
  apply average_nonneg
  intro ω
  split <;> norm_num

theorem probability_le_one [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability p ≤ 1 := by
  calc
    probability p ≤ average (fun _ : Ω => 1) := by
      apply average_mono
      intro ω
      split <;> norm_num
    _ = 1 := average_const _

theorem probability_mono (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ ω, p ω → q ω) : probability p ≤ probability q := by
  apply average_mono
  intro ω
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · simp only [ite_eq_right hp]
    split <;> norm_num

theorem probability_not [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability (fun ω => ¬ p ω) = 1 - probability p := by
  have he : (fun ω => if ¬ p ω then (1 : ℚ) else 0) =
      (fun ω => 1 - if p ω then (1 : ℚ) else 0) := by
    funext ω
    by_cases h : p ω <;> simp [h]
  unfold probability
  rw [he, average_sub, average_const]

/-- A bijection swapping an event with its complement proves exact half
probability. At a leaf the bijection is translation by a symbol on which a
nonzero binary character is one. -/
theorem probability_eq_half_of_swap [Nonempty Ω]
    (p : Ω → Prop) [DecidablePred p] (e : Ω ≃ Ω)
    (hswap : ∀ ω, p (e ω) ↔ ¬ p ω) : probability p = 1 / 2 := by
  have he : probability (fun ω => ¬ p ω) = probability p := by
    apply Fintype.expect_equiv e
    intro ω
    simp only [hswap ω]
  rw [probability_not] at he
  linarith

/-- Every nonzero binary additive character detects precisely half of uniform
symbols. The witness may depend on the previously sampled path. -/
theorem binary_character_detection_probability [AddGroup Ω]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0) :
    probability (fun ω => χ ω ≠ 0) = 1 / 2 := by
  apply probability_eq_half_of_swap _ (Equiv.addLeft v)
  intro ω
  change χ (v + ω) ≠ 0 ↔ ¬χ ω ≠ 0
  rw [map_add]
  generalize ha : χ v = a at hv ⊢
  generalize hb : χ ω = b
  fin_cases a <;> fin_cases b
  · exact (hv rfl).elim
  · exact (hv rfl).elim
  · change (1 : ZMod 2) + 0 ≠ 0 ↔ ¬ (0 : ZMod 2) ≠ 0
    decide
  · change (1 : ZMod 2) + 1 ≠ 0 ↔ ¬ (1 : ZMod 2) ≠ 0
    decide

/-- A surviving family contains a nonzero character, so its detection event
contains an event of exact half probability. -/
theorem binary_family_detection_ge_half [AddGroup Ω]
    (detects : Ω → Prop) [DecidablePred detects]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0)
    (hcontains : ∀ ω, χ ω ≠ 0 → detects ω) :
    (1 / 2 : ℚ) ≤ probability detects := by
  rw [← binary_character_detection_probability χ v hv]
  exact probability_mono _ _ hcontains

theorem harmonic_nonneg (r : ℕ) : 0 ≤ harmonic r := by
  induction r with
  | zero => simp
  | succ r ih => rw [harmonic_succ]; positivity

theorem harmonic_mono {r s : ℕ} (h : r ≤ s) : harmonic r ≤ harmonic s := by
  induction h with
  | refl => exact le_rfl
  | @step s h ih =>
    rw [harmonic_succ]
    have : (0 : ℚ) ≤ (↑(s + 1))⁻¹ := by positivity
    linarith

theorem harmonic_pos {r : ℕ} (h : 0 < r) : 0 < harmonic r := by
  have hm := harmonic_mono (r := 1) (s := r) h
  norm_num [harmonic_succ] at hm
  linarith

theorem harmonic_sub_predecessor {r : ℕ} (h : 0 < r) :
    harmonic r - harmonic (r - 1) = (r : ℚ)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [harmonic_succ]

/-- A generic rank-`r` space loses either zero or one dimension. Its harmonic
drop is exactly the loss indicator times `1/r`. -/
theorem generic_drop_identity (r : ℕ) (next : Ω → ℕ) (hr : 0 < r)
    (hstep : ∀ ω, next ω = r ∨ next ω = r - 1) :
    average (fun ω => harmonic r - harmonic (next ω)) =
      (r : ℚ)⁻¹ * probability (fun ω => next ω < r) := by
  have he : (fun ω => harmonic r - harmonic (next ω)) =
      (fun ω => (r : ℚ)⁻¹ * if next ω < r then 1 else 0) := by
    funext ω
    rcases hstep ω with h | h
    · simp [h]
    · rw [h, ite_eq_left (Nat.sub_lt hr (by omega))]
      simp [harmonic_sub_predecessor hr]
  rw [he, average_mul_left]
  rfl

/-- The generic loss probability `3rθ` becomes the rank-independent harmonic
loss bound `3θ`. -/
theorem generic_expected_drop_le (r : ℕ) (next : Ω → ℕ) (θ : ℚ)
    (hr : 0 < r) (hstep : ∀ ω, next ω = r ∨ next ω = r - 1)
    (hloss : probability (fun ω => next ω < r) ≤ 3 * r * θ) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ 3 * θ := by
  rw [generic_drop_identity r next hr hstep]
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  calc
    (r : ℚ)⁻¹ * probability (fun ω => next ω < r) ≤
        (r : ℚ)⁻¹ * (3 * r * θ) :=
      mul_le_mul_of_nonneg_left hloss (le_of_lt (inv_pos.mpr hrq))
    _ = 3 * θ := by field_simp [ne_of_gt hrq]

/-- Without genericity, charge the entire harmonic potential only on paths
where some rank is lost. -/
theorem arbitrary_expected_drop_le (r : ℕ) (next : Ω → ℕ) (p : ℚ)
    (hstep : ∀ ω, next ω ≤ r)
    (hloss : probability (fun ω => next ω < r) ≤ p) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ harmonic r * p := by
  calc
    average (fun ω => harmonic r - harmonic (next ω)) ≤
        average (fun ω => harmonic r * if next ω < r then 1 else 0) := by
      apply average_mono
      intro ω
      by_cases h : next ω < r
      · simp only [ite_eq_left h, mul_one]
        exact sub_le_self _ (harmonic_nonneg _)
      · have he : next ω = r := by have := hstep ω; omega
        simp [he]
    _ = harmonic r * probability (fun ω => next ω < r) := by
      rw [average_mul_left]
      rfl
    _ ≤ harmonic r * p := mul_le_mul_of_nonneg_left hloss (harmonic_nonneg _)

/-- Averaging a conditional rank-loss estimate uses only a bound on the bad
space's probability, even when the selected lift depends on that space. -/
theorem expected_drop_le_four_theta [Nonempty Ω]
    (drop : Ω → ℚ) (bad : Ω → Prop) [DecidablePred bad] (C θ ε : ℚ)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hconditional : ∀ ω, drop ω ≤ 3 * θ + C * θ * if bad ω then 1 else 0)
    (hbad : probability bad ≤ ε) (hsmall : C * ε ≤ 1) :
    average drop ≤ 4 * θ := by
  have haverage : average drop ≤ 3 * θ + C * θ * probability bad := by
    calc
      average drop ≤ average (fun ω => 3 * θ + C * θ * if bad ω then 1 else 0) :=
        average_mono hconditional
      _ = 3 * θ + C * θ * probability bad := by
        rw [average_add, average_const, average_mul_left]
        rfl
  have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
  nlinarith

def badRankCoefficient (r₀ : ℕ) : ℚ := harmonic r₀ * 2 ^ r₀

theorem badRankCoefficient_nonneg (r₀ : ℕ) : 0 ≤ badRankCoefficient r₀ := by
  exact mul_nonneg (harmonic_nonneg _) (by positivity)

def depth (r₀ : ℕ) (θ : ℚ) : ℕ := ⌊harmonic r₀ / (8 * θ)⌋₊

theorem depth_budget (r₀ : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    4 * (depth r₀ θ : ℚ) * θ ≤ harmonic r₀ / 2 := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.floor_le (div_nonneg (harmonic_nonneg r₀) (le_of_lt hden))
  have hb := (le_div_iff₀ hden).mp hf
  change (depth r₀ θ : ℚ) * (8 * θ) ≤ harmonic r₀ at hb
  nlinarith

/-- Expected harmonic losses telescope. The ranks may be arbitrary functions
of the full path; this assertion introduces no independence premise. -/
theorem expected_total_drop_le [Nonempty Ω] (rank : ℕ → Ω → ℕ)
    (r₀ s : ℕ) (θ : ℚ) (hinitial : ∀ ω, rank 0 ω = r₀)
    (hstep : ∀ j < s,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) ≤ 4 * θ) :
    harmonic r₀ - average (fun ω => harmonic (rank s ω)) ≤ 4 * s * θ := by
  have haux : ∀ n, n ≤ s →
      harmonic r₀ - average (fun ω => harmonic (rank n ω)) ≤ 4 * n * θ := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [hinitial, average_const, Nat.cast_zero, mul_zero, zero_mul, sub_self, le_refl]
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hnext := hstep n (by omega)
      rw [average_sub] at hnext
      push_cast
      linarith
  exact haux s le_rfl

/-- The potential-to-survival step needs only the final finite experiment,
allowing earlier levels to have different path sample spaces. -/
theorem survival_probability_ge_half_of_potential (rank : Ω → ℕ) (r₀ : ℕ)
    (hr₀ : 0 < r₀) (hterminal : ∀ ω, rank ω ≤ r₀)
    (hmean : harmonic r₀ / 2 ≤ average (fun ω => harmonic (rank ω))) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank ω) := by
  have hpoint : average (fun ω => harmonic (rank ω)) ≤
      harmonic r₀ * probability (fun ω => 0 < rank ω) := by
    calc
      average (fun ω => harmonic (rank ω)) ≤
          average (fun ω => harmonic r₀ * if 0 < rank ω then 1 else 0) := by
        apply average_mono
        intro ω
        by_cases h : 0 < rank ω
        · simpa only [ite_eq_left h, mul_one] using harmonic_mono (hterminal ω)
        · have he : rank ω = 0 := by omega
          simp [he]
      _ = harmonic r₀ * probability (fun ω => 0 < rank ω) := by
        rw [average_mul_left]
        rfl
  have hpos := harmonic_pos hr₀
  nlinarith

/-- At depth `s` with `4sθ ≤ H(r₀)/2`, at least half the paths have nonzero
terminal rank. The terminal bound follows from rank monotonicity in the actual
gadget, and is kept explicit here. -/
theorem survival_probability_ge_half [Nonempty Ω] (rank : ℕ → Ω → ℕ)
    (r₀ s : ℕ) (θ : ℚ) (hr₀ : 0 < r₀)
    (hinitial : ∀ ω, rank 0 ω = r₀)
    (hterminal : ∀ ω, rank s ω ≤ r₀)
    (hstep : ∀ j < s,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) ≤ 4 * θ)
    (hdepth : 4 * s * θ ≤ harmonic r₀ / 2) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank s ω) := by
  have htotal := expected_total_drop_le rank r₀ s θ hinitial hstep
  apply survival_probability_ge_half_of_potential (rank s) r₀ hr₀ hterminal
  linarith

/-- Direct assembly of the adaptive calculation. `conditionalDrop` is the
conditional mean after fixing the history; `hmean` is the finite averaging
identity. The only assertion about bad orientations is their probability
bound, so a future lift is allowed to depend on the incoming orientation. -/
theorem survival_of_adaptive_step_law [Nonempty Ω]
    (rank : ℕ → Ω → ℕ) (bad : ℕ → Ω → Prop)
    [∀ j, DecidablePred (bad j)] (conditionalDrop : ℕ → Ω → ℚ)
    (r₀ : ℕ) (θ ε : ℚ) (hr₀ : 0 < r₀) (hθ : 0 < θ)
    (hinitial : ∀ ω, rank 0 ω = r₀)
    (hterminal : ∀ ω, rank (depth r₀ θ) ω ≤ r₀)
    (hmean : ∀ j < depth r₀ θ,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) =
        average (conditionalDrop j))
    (hconditional : ∀ j < depth r₀ θ, ∀ ω,
      conditionalDrop j ω ≤ 3 * θ + badRankCoefficient r₀ * θ *
        if bad j ω then 1 else 0)
    (hbad : ∀ j < depth r₀ θ, probability (bad j) ≤ ε)
    (hsmall : badRankCoefficient r₀ * ε ≤ 1) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank (depth r₀ θ) ω) := by
  apply survival_probability_ge_half rank r₀ (depth r₀ θ) θ hr₀ hinitial hterminal
  · intro j hj
    rw [hmean j hj]
    exact expected_drop_le_four_theta (conditionalDrop j) (bad j)
      (badRankCoefficient r₀) θ ε (badRankCoefficient_nonneg r₀)
      (le_of_lt hθ) (hconditional j hj) (hbad j hj) hsmall
  · exact depth_budget r₀ θ hθ

/-- A final independent uniform symbol detects a surviving character with
probability at least one half. Multiplying this conditional bound by the
surviving-path probability gives the required quarter. -/
theorem detection_probability_ge_quarter [Nonempty Ω]
    (survives : Ω → Prop) [DecidablePred survives] (conditionalDetection : Ω → ℚ)
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hnonneg : ∀ ω, 0 ≤ conditionalDetection ω)
    (hdetect : ∀ ω, survives ω → (1 / 2 : ℚ) ≤ conditionalDetection ω) :
    (1 / 4 : ℚ) ≤ average conditionalDetection := by
  have h : (1 / 2 : ℚ) * probability survives ≤ average conditionalDetection := by
    calc
      (1 / 2 : ℚ) * probability survives =
          average (fun ω => (1 / 2 : ℚ) * if survives ω then 1 else 0) :=
        (average_mul_left _ _).symm
      _ ≤ average conditionalDetection := by
        apply average_mono
        intro ω
        by_cases hs : survives ω
        · simpa only [ite_eq_left hs, mul_one] using hdetect ω hs
        · simpa only [ite_eq_right hs, mul_zero] using hnonneg ω
  linarith

/-- Uniform paths and a separately sampled uniform terminal symbol have the
product law used in the leaf-noise experiment. -/
theorem probability_product {Ξ : Type*} [Fintype Ξ]
    (detects : Ω × Ξ → Prop) [DecidablePred detects] :
    probability detects = average (fun ω => probability (fun ξ => detects (ω, ξ))) := by
  unfold probability average
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ)
      (fun z => if detects z then (1 : ℚ) else 0))

theorem product_detection_probability_ge_quarter [Nonempty Ω]
    {Ξ : Type*} [Fintype Ξ]
    (survives : Ω → Prop) [DecidablePred survives]
    (detects : Ω × Ξ → Prop) [DecidablePred detects]
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hdetect : ∀ ω, survives ω →
      (1 / 2 : ℚ) ≤ probability (fun ξ => detects (ω, ξ))) :
    (1 / 4 : ℚ) ≤ probability detects := by
  rw [probability_product]
  exact detection_probability_ge_quarter survives _ hsurvival
    (fun ω => probability_nonneg _) hdetect

/-- Terminal family detection with actual binary characters rather than an
assumed conditional probability bound. A character can be selected separately
on every surviving path. -/
theorem binary_product_detection_probability_ge_quarter [Nonempty Ω]
    {Ξ : Type*} [Fintype Ξ] [AddGroup Ξ]
    (survives : Ω → Prop) [DecidablePred survives]
    (detects : Ω × Ξ → Prop) [DecidablePred detects]
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hcharacter : ∀ ω, survives ω → ∃ χ : Ξ →+ ZMod 2, ∃ v : Ξ,
      χ v ≠ 0 ∧ ∀ ξ, χ ξ ≠ 0 → detects (ω, ξ)) :
    (1 / 4 : ℚ) ≤ probability detects := by
  apply product_detection_probability_ge_quarter survives detects hsurvival
  intro ω hω
  obtain ⟨χ, v, hv, hcontains⟩ := hcharacter ω hω
  exact binary_family_detection_ge_half (fun ξ => detects (ω, ξ)) χ v hv hcontains

end MaxCutGames.Gadget.Harmonic

end

end OAI
