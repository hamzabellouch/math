import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.FunLike.Fintype
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.Quadratic.BlockCounting
import OAI.Computability.UniqueGames.Quadratic.BlockDimension
import OAI.Computability.UniqueGames.Quadratic.BlockNoise

namespace OAI

section

/-! Exact rational expectation for the quadratic block's conditioned noise. -/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The uniform noise space after conditioning the perturbation to be nonzero. -/
abbrev NonzeroBlock (v : Vec F) := {u : U v // u ≠ 0}

/-- Exact uniform expectation of the nonlinear-change indicator. -/
def nonzeroBlockChangeProbability (v : Vec F) (p : Vec F × Vec F) : ℚ := by
  classical
  exact Finset.univ.expect fun u : NonzeroBlock v =>
    if blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p then 1 else 0

/-- The zero perturbation is never a changed perturbation, so conditioning
does not remove any element from the change event. -/
def conditionedChangedEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : NonzeroBlock v //
      blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p} ≃
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} where
  toFun u := ⟨u.val.val, u.property⟩
  invFun u := ⟨⟨u.val, blockObservable_change_ne_zero v p u.val u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nonzeroBlockChangeProbability_eq_count (v : Vec F) (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      (Nat.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} : ℚ) /
      (Nat.card (NonzeroBlock v) : ℚ) := by
  classical
  have hcard :
      (Finset.univ.filter (fun u : NonzeroBlock v =>
        blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p)).card =
      Fintype.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (conditionedChangedEquiv v p)
  simp only [nonzeroBlockChangeProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, hcard, Nat.card_eq_fintype_card]

/-- The one-level change probability is exactly `1-θ`, for every fixed input.
Here `θ = 1/(q²+q+1)` and `q` is the actual finite-field cardinality. -/
theorem nonzeroBlockChangeProbability_eq (v : Vec F) (hv : v ≠ 0)
    (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [nonzeroBlockChangeProbability_eq_count, natCard_block_changes v hv p]
  change ((Nat.card F * (Nat.card F ^ 2 - 1) : ℕ) : ℚ) /
    (Nat.card {u : U v // u ≠ 0} : ℚ) = _
  rw [natCard_nonzero_U v hv]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqpos : 0 < Nat.card F := lt_trans Nat.zero_lt_one hq
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ hqpos
  have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow 3 _ hqpos
  have hq' : (1 : ℚ) < Nat.card F := by exact_mod_cast hq
  simpa only [Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_sub hq3,
    Nat.cast_pow, Nat.cast_one] using block_change_ratio (Nat.card F) hq'

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- An orientation identifies the common binary alphabet with a line's block. -/
abbrev BlockOrientation (A : FieldLine F) :=
  Vec F ≃ₗ[ZMod 2] U (lineGenerator A)

noncomputable instance fieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _

instance finiteBlockOrientation (A : FieldLine F) : Finite (BlockOrientation A) :=
  DFunLike.finite _

noncomputable instance blockOrientationFintype (A : FieldLine F) :
    Fintype (BlockOrientation A) := Fintype.ofFinite _

/-- Existence uses the proved dimension of the actual quadratic block. -/
noncomputable def chosenBlockOrientation (A : FieldLine F) : BlockOrientation A :=
  LinearEquiv.ofFinrankEq (Vec F) (U (lineGenerator A))
    (finrank_U_eq_finrank_vec (lineGenerator A) (lineGenerator_ne_zero A)).symm

/-- Composing with one fixed orientation identifies all orientations with
automorphisms of the common binary alphabet. -/
noncomputable def blockOrientationEquiv (A : FieldLine F) :
    BlockOrientation A ≃ (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun J := J.trans (chosenBlockOrientation A).symm
  invFun J := J.trans (chosenBlockOrientation A)
  left_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).apply_symm_apply (J x)
  right_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).symm_apply_apply (J x)

theorem card_blockOrientation (A : FieldLine F) :
    Nat.card (BlockOrientation A) = Nat.card (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Nat.card_congr (blockOrientationEquiv A)

theorem card_blockOrientation_eq (A B : FieldLine F) :
    Nat.card (BlockOrientation A) = Nat.card (BlockOrientation B) := by
  rw [card_blockOrientation, card_blockOrientation]

theorem card_blockOrientation_pos (A : FieldLine F) :
    0 < Nat.card (BlockOrientation A) := by
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  exact Nat.card_pos

abbrev BlockOrientationIndex (F : Type*) [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] := Σ A : FieldLine F, BlockOrientation A

noncomputable def blockOrientationIndexEquiv :
    BlockOrientationIndex F ≃ FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun p := (p.1, blockOrientationEquiv p.1 p.2)
  invFun p := ⟨p.1, (blockOrientationEquiv p.1).symm p.2⟩
  left_inv := by
    rintro ⟨A, J⟩
    simp
  right_inv := by
    rintro ⟨A, J⟩
    simp

theorem card_blockOrientationIndex :
    Nat.card (BlockOrientationIndex F) =
      (Nat.card F ^ 2 + Nat.card F + 1) * Nat.card (Vec F ≃ₗ[ZMod 2] Vec F) := by
  rw [Nat.card_congr (blockOrientationIndexEquiv (F := F)), Nat.card_prod, card_FieldLine]

end UniqueGamesTheorem.Quadratic

end

end OAI
