import OAI.Computability.UniqueGames.Gadgets.ConcatenationLemmas
import OAI.Computability.UniqueGames.Quadratic.AlignmentCertificateLemmas
import OAI.Computability.UniqueGames.Quadratic.Block
import OAI.Computability.UniqueGames.Quadratic.BlockNoiseProbabilityLemmas
import OAI.Computability.UniqueGames.Quadratic.BlockSpanLemmas
import OAI.Computability.UniqueGames.Quadratic.BlockTrace

namespace OAI

section

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
/-- A field-valued identity before applying the binary trace. -/
theorem dot_Q_smul (z : Vec F) (t : F) :
    dot z (Q (t • z)) = t ^ 2 * (z 0 * z 1 * z 2) := by
  change z 0 * ((t * z 1) * (t * z 2)) +
      z 1 * ((t * z 0) * (t * z 2)) +
      z 2 * ((t * z 0) * (t * z 1)) = _
  calc
    _ = (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- The binary character with separate horizontal and vertical coefficients. -/
noncomputable def blockCharacter (g z : Vec F) (p : Vec F × Vec F) : ZMod 2 :=
  traceBinary (dot g p.1 + dot z p.2)

/-- Literal annihilation of every vector in the block attached to `v`. -/
def BlockAnnihilates (g z v : Vec F) : Prop :=
  ∀ p ∈ U v, blockCharacter g z p = 0

omit [Finite F] in
theorem blockCharacter_on_quadratic (g z : Vec F) (t : F) :
    blockCharacter g z (t • z, Q (t • z)) =
      traceBinary (t * dot g z + t ^ 2 * (z 0 * z 1 * z 2)) := by
  simp only [blockCharacter, dot_smul_right, dot_Q_smul]

/-- The exact quadratic-block kernel criterion on the line of the character. -/
theorem blockAnnihilates_self_iff (g z : Vec F) :
    BlockAnnihilates g z z ↔ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    apply (trace_quadratic_vanish_iff _ _).mp
    intro t
    have hm : (t • z, Q (t • z)) ∈ U z := by
      simpa only [add_zero] using pair_mem_U z (t • z) 0
        ((mem_line_iff z (t • z)).mpr ⟨t, rfl⟩) (Submodule.zero_mem _)
    simpa only [blockCharacter_on_quadratic] using h _ hm
  · intro h p hp
    obtain ⟨a, ha, w, hw, rfl⟩ := (mem_U_iff_exists z p).mp hp
    obtain ⟨t, rfl⟩ := (mem_line_iff z a).mp ha
    change traceBinary (dot g (t • z) + dot z (Q (t • z) + w)) = 0
    rw [dot_add_right, (mem_hyperplane z w).mp hw, add_zero,
      dot_smul_right, dot_Q_smul]
    exact (trace_quadratic_vanish_iff _ _).mpr h t

omit [Finite F] in
/-- The binary block is independent of the nonzero generator of its field line. -/
theorem U_smul_ne_zero (v : Vec F) {t : F} (ht : t ≠ 0) : U (t • v) = U v := by
  have hl : line (t • v) = line v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v
  ext p
  simp only [mem_U, hl, dot_smul_left, mul_eq_zero, ht, false_or]

omit [Finite F] in
theorem U_eq_of_nonzero_mem_line {v z : Vec F} (hz : z ≠ 0)
    (hm : z ∈ line v) : U z = U v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hm
  have ht : t ≠ 0 := by
    intro ht
    apply hz
    simp [ht]
  exact U_smul_ne_zero v ht

/-- A character in a block's kernel has its vertical coefficient on that line. -/
theorem mem_line_of_blockAnnihilates {g z v : Vec F} (hv : v ≠ 0)
    (h : BlockAnnihilates g z v) : z ∈ line v := by
  apply (trace_annihilator_hyperplane_iff_mem_line hv).mp
  intro y hy
  have hm : (0, y) ∈ U v := by
    simpa only [Q_zero, zero_add] using
      pair_mem_U v 0 y (Submodule.zero_mem _) hy
  simpa only [blockCharacter, dot_zero_right, zero_add] using h _ hm

/-- Full nonzero-character criterion, including the field-line condition. -/
theorem blockAnnihilates_iff {g z v : Vec F} (hv : v ≠ 0) (hz : z ≠ 0) :
    BlockAnnihilates g z v ↔
      z ∈ line v ∧ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    have hm := mem_line_of_blockAnnihilates hv h
    refine ⟨hm, (blockAnnihilates_self_iff g z).mp ?_⟩
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h
  · rintro ⟨hm, ha⟩
    have h := (blockAnnihilates_self_iff g z).mpr ha
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h

end UniqueGamesTheorem.Quadratic

end

section

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [Fintype (BlockOrientationIndex F)]

def blockEmbedding (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def blockAggregate : (BlockOrientationIndex F → Vec F) →ₗ[ZMod 2] Vec F × Vec F :=
  Gadget.aggregate (blockEmbedding (F := F))

theorem blockAggregate_single [DecidableEq (BlockOrientationIndex F)]
    (i : BlockOrientationIndex F) (b : Vec F) :
    blockAggregate (Pi.single i b) = blockEmbedding i b := by
  classical
  change (∑ j : BlockOrientationIndex F,
    blockEmbedding j ((Pi.single i b : BlockOrientationIndex F → Vec F) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fieldLine_block_le_range_aggregate (A : FieldLine F) :
    U (lineGenerator A) ≤ LinearMap.range (blockAggregate (F := F)) := by
  classical
  intro p hp
  let J := chosenBlockOrientation A
  let i : BlockOrientationIndex F := ⟨A, J⟩
  obtain ⟨b, hb⟩ := J.surjective ⟨p, hp⟩
  refine ⟨Pi.single i b, ?_⟩
  rw [blockAggregate_single]
  change ((J b : U (lineGenerator A)) : Vec F × Vec F) = p
  exact congrArg Subtype.val hb

/-- All blocks occur in the actual pair-indexed aggregate.  Their already
proved span is the entire horizontal/vertical space, so the aggregate is
surjective, as required by the recursive shift construction. -/
theorem blockAggregate_surjective : Function.Surjective (blockAggregate (F := F)) := by
  have hspan : (⨆ v : {v : Vec F // v ≠ 0}, U v.1) ≤
      LinearMap.range (blockAggregate (F := F)) := by
    apply iSup_le
    intro v
    let A : FieldLine F := Projectivization.mk F v.1 v.2
    have hl : line (lineGenerator A) = line v.1 := by
      simpa only [A, Projectivization.submodule_mk, line] using line_lineGenerator A
    have hm : lineGenerator A ∈ line v.1 := by
      rw [← hl]
      exact (mem_line_iff _ _).mpr ⟨1, one_smul _ _⟩
    have hu := U_eq_of_nonzero_mem_line (lineGenerator_ne_zero A) hm
    simpa only [hu] using fieldLine_block_le_range_aggregate A
  rw [iSup_U_nonzero_eq_top] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem aggregate_blockEmbedding_surjective :
    Function.Surjective (Gadget.aggregate (blockEmbedding (F := F))) :=
  blockAggregate_surjective

end UniqueGamesTheorem.Quadratic

end

end

end OAI
