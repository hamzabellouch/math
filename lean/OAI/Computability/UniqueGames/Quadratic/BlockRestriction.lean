import OAI.Computability.UniqueGames.Quadratic.BlockKernelLemmas
import OAI.Computability.UniqueGames.Quadratic.GenericSeparationLemmas

namespace OAI

section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem dot_add_first (x y z : Vec F) :
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
      blockCharacter, dot_add_first, map_add]
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

end UniqueGamesTheorem.Quadratic

end

end OAI
