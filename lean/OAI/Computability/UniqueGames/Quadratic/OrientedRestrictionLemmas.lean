import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dual.Defs
import OAI.Computability.UniqueGames.Quadratic.BlockNoiseProbabilityLemmas
import OAI.Computability.UniqueGames.Quadratic.BlockRestriction

namespace OAI

section

/-!
# Orientation-independent character kernels

Changing the binary parametrization of a block only pulls its dual back along
a linear equivalence.  This leaves the logical kernel unchanged and places
all child maps in one fixed dual space for the finite counting argument.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

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

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# At most `3r` actual lossy field lines

The genericity bound applies to the common-parent lift before a line or an
orientation is chosen.  A nonzero kernel character determines exactly one
projective field line, and its actual kernel equation implies alignment.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

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

end

end UniqueGamesTheorem.Quadratic

end

end OAI
