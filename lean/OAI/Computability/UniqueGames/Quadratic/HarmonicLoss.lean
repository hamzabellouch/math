import Mathlib.FieldTheory.Finiteness
import OAI.Computability.UniqueGames.Gadgets.ConcatenationLemmas
import OAI.Computability.UniqueGames.Quadratic.OrientedRestrictionLemmas

namespace OAI

section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Harmonic

noncomputable section

private theorem exists_nonzero_kernel_of_range_rank_lt
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    (f : V →ₗ[ZMod 2] W)
    (h : Module.finrank (ZMod 2) f.range < Module.finrank (ZMod 2) V) :
    ∃ z, z ≠ 0 ∧ f z = 0 := by
  by_contra hn
  have hk : f.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hz0
    exact hn ⟨z, hz0, hz⟩
  have hdim := f.finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hdim
  omega

private theorem probability_rank_drop_le_loss_count
    {I V W : Type*} [Fintype I] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : I → V →ₗ[ZMod 2] W) :
    probability (fun i => Module.finrank (ZMod 2) (f i).range <
        Module.finrank (ZMod 2) V) ≤
      ((lossIndices f).card : ℚ) / Fintype.card I := by
  classical
  have hsub : Finset.univ.filter (fun i =>
      Module.finrank (ZMod 2) (f i).range < Module.finrank (ZMod 2) V) ⊆
      lossIndices f := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      exists_nonzero_kernel_of_range_rank_lt (f i) (Finset.mem_filter.mp hi).2⟩
  simp only [probability, average, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Fintype (FieldLine F) := Fintype.ofFinite _
local instance (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

def fieldLineTheta (F : Type*) [Field F] [Finite F] : ℚ :=
  (Nat.card (FieldLine F) : ℚ)⁻¹

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem fieldLineTheta_eq : fieldLineTheta F =
    ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ :=
  reciprocal_card_FieldLine

/-- The image dimension of the actual oriented child restriction map. -/
def nextBlockRank (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : ℕ :=
  Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).range

theorem nextBlockRank_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A ≤ Module.finrank (ZMod 2) S :=
  LinearMap.finrank_range_le _

/-- Changing the binary orientation of every child leaves its logical image rank unchanged. -/
theorem nextBlockRank_independent (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J J' : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A = nextBlockRank S g J' A := by
  have hk : (fieldLineRestrictions S g J A).ker =
      (fieldLineRestrictions S g J' A).ker :=
    ker_orientedBlockRestriction_independent S g (lineGenerator A) (J A) (J' A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  have hdim' := (fieldLineRestrictions S g J' A).finrank_range_add_finrank_ker
  rw [hk] at hdim
  unfold nextBlockRank
  omega

theorem generic_nextBlockRank_dichotomy (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) (A : FieldLine F) :
    nextBlockRank S g J A = Module.finrank (ZMod 2) S ∨
      nextBlockRank S g J A = Module.finrank (ZMod 2) S - 1 := by
  have hk := finrank_ker_orientedBlockRestriction_le_one S g
    (lineGenerator_ne_zero A) hS (J A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).ker ≤ 1 at hk
  unfold nextBlockRank
  omega

theorem generic_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      3 * Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count (fieldLineRestrictions S g J)
    _ ≤ (3 * (Module.finrank (ZMod 2) S : ℚ)) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_loss_fieldLineRestrictions_le_three_rank S g J hS
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

/-- Actual generic block restrictions have rank-independent expected harmonic loss. -/
theorem generic_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    average (fun A => harmonic (Module.finrank (ZMod 2) S) -
      harmonic (nextBlockRank S g J A)) ≤ 3 * fieldLineTheta F := by
  classical
  by_cases hr : 0 < Module.finrank (ZMod 2) S
  · exact generic_expected_drop_le _ _ _ hr
      (generic_nextBlockRank_dichotomy S g J hS)
      (generic_block_loss_probability_le S g J hS)
  · have hr0 : Module.finrank (ZMod 2) S = 0 := by omega
    have hnext : ∀ A, nextBlockRank S g J A = 0 := by
      intro A
      have := nextBlockRank_le S g J A
      omega
    simp only [hr0, hnext, harmonic_zero, sub_self]
    have hzero : average (fun _ : FieldLine F => (0 : ℚ)) = 0 := by
      simp [average]
    rw [hzero]
    unfold fieldLineTheta
    positivity

theorem card_loss_fieldLineRestrictions_le_nonzero
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤ Fintype.card S - 1 := by
  classical
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    exact one_ne_zero (congrFun h 0))
  apply card_lossIndices_le_nonzero (fieldLineRestrictions S g J)
    (fun z : S => characterFieldLine A₀ (z : Vec F))
  intro A z hz hzero
  have hk := (mem_ker_orientedBlockRestriction_iff S g
    (lineGenerator_ne_zero A) (J A) hz).mp hzero
  exact characterFieldLine_eq_of_mem (fun h => hz (Subtype.ext h)) hk.1

theorem arbitrary_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  have hc : Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
    simpa only [ZMod.card] using Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  have hcount : (lossIndices (fieldLineRestrictions S g J)).card ≤
      2 ^ Module.finrank (ZMod 2) S :=
    (card_loss_fieldLineRestrictions_le_nonzero S g J).trans
      ((Nat.sub_le _ _).trans_eq hc)
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count (fieldLineRestrictions S g J)
    _ ≤ ((2 : ℚ) ^ Module.finrank (ZMod 2) S) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem arbitrary_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    average (fun A => harmonic (Module.finrank (ZMod 2) S) -
      harmonic (nextBlockRank S g J A)) ≤
        harmonic (Module.finrank (ZMod 2) S) *
          2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  simpa only [mul_assoc] using arbitrary_expected_drop_le
    (Module.finrank (ZMod 2) S) (nextBlockRank S g J)
    (2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F)
    (nextBlockRank_le S g J) (arbitrary_block_loss_probability_le S g J)

end

end UniqueGamesTheorem.Quadratic

end

end OAI
