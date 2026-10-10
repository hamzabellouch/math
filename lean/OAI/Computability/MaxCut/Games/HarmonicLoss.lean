import Mathlib
import OAI.Computability.MaxCut.Games.BlockRestriction

namespace OAI

noncomputable section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the MaxCutGames.Gadget.Harmonic.harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

namespace MaxCutGames.Quadratic

open scoped BigOperators
open MaxCutGames.Gadget.Harmonic

private theorem exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss
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

private theorem probability_rank_drop_le_loss_count_inline_HarmonicLoss
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
      exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss (f i) (Finset.mem_filter.mp hi).2⟩
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
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ (3 * (Module.finrank (ZMod 2) S : ℚ)) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_loss_fieldLineRestrictions_le_three_rank S g J hS
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

/-- Actual generic block restrictions have rank-independent expected MaxCutGames.Gadget.Harmonic.harmonic loss. -/
theorem generic_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    average (fun A => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      MaxCutGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤ 3 * fieldLineTheta F := by
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
    simp only [hr0, hnext, MaxCutGames.Gadget.Harmonic.harmonic_zero, sub_self]
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
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ ((2 : ℚ) ^ Module.finrank (ZMod 2) S) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem arbitrary_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    average (fun A => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      MaxCutGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤
        MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) *
          2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  simpa only [mul_assoc] using arbitrary_expected_drop_le
    (Module.finrank (ZMod 2) S) (nextBlockRank S g J)
    (2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F)
    (nextBlockRank_le S g J) (arbitrary_block_loss_probability_le S g J)

end MaxCutGames.Quadratic

/-!
# Outgoing MaxCutGames.Gadget.Harmonic.harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

namespace MaxCutGames.Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
local instance : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) := Fintype.ofFinite _

def outgoingLoss (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : ℚ :=
  average (fun i : BlockOrientationIndex F => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
    MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ i).range))

/-- Averaging all binary orientations reduces exactly to the actual line-law
rank experiment, after transporting logical characters by the trace pairing. -/
theorem outgoingLoss_eq_line_average
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ = average (fun A : FieldLine F =>
      MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        MaxCutGames.Gadget.Harmonic.harmonic (nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A)) := by
  unfold outgoingLoss average
  rw [mean_block_pairs]
  apply Finset.expect_congr rfl
  intro A _
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  have hrank (J : BlockOrientation A) :
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
        nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A := by
    rw [childCharacter_rank_independent S γ A J (chosenBlockOrientation A)]
    rw [childCharacter_range_eq]
    rfl
  simp_rw [hrank]
  exact Finset.expect_const Finset.univ_nonempty _

/-- The generic all-lifts bound applies to the actual common parent map. -/
theorem generic_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (hS : IsGeneric (traceSpace S)) :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank] using
    generic_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation hS

/-- Nongeneric actual child maps satisfy the fallback MaxCutGames.Gadget.Harmonic.harmonic charge. -/
theorem arbitrary_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank, badRankCoefficient] using
    arbitrary_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation

theorem badRankCoefficient_mono {r s : ℕ} (h : r ≤ s) :
    badRankCoefficient r ≤ badRankCoefficient s := by
  unfold badRankCoefficient
  apply mul_le_mul (harmonic_mono h) (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h)
  · positivity
  · exact harmonic_nonneg _

/-- Combined conditional law with a coefficient frozen at the initial rank.
The bad predicate is exactly the nongeneric trace-coordinate domain. -/
theorem outgoing_harmonic_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (r₀ : ℕ)
    (hcap : Module.finrank (ZMod 2) S ≤ r₀)
    [Decidable (IsGeneric (traceSpace S))] :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F +
      badRankCoefficient r₀ * fieldLineTheta F * if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  have hθ : 0 ≤ fieldLineTheta F := by unfold fieldLineTheta; positivity
  by_cases hS : IsGeneric (traceSpace S)
  · simpa only [not_true_eq_false, hS, ite_false, mul_zero, add_zero] using
      generic_outgoing_loss_le S γ hS
  · rw [ite_eq_left hS, mul_one]
    calc
      outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F :=
        arbitrary_outgoing_loss_le S γ
      _ ≤ badRankCoefficient r₀ * fieldLineTheta F :=
        mul_le_mul_of_nonneg_right (badRankCoefficient_mono hcap) hθ
      _ ≤ 3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F := by linarith

/-- Direct instantiation of `DescentProbability.expected_terminal_loss`'s
outgoing-step hypothesis for the concrete child domain of every actual lift. -/
theorem descendant_harmonic_loss_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S) (r₀ : ℕ)
      (_hcap : Module.finrank (ZMod 2) S ≤ r₀)
      [Decidable (IsGeneric (traceSpace S))],
      average (fun i : BlockOrientationIndex F => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (Descent.childDomain J hJ Q s S L i))) ≤
        3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F *
          if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  intro J hJ Q s S L r₀ hcap hdec
  exact outgoing_harmonic_loss_le S (Descent.commonGamma J hJ Q s S L) r₀ hcap

end MaxCutGames.Gadget.OutgoingHarmonic

/-!
# The finite nongeneric fraction

This definition records the actual uniform event on the rank-indexed
Grassmannian. Its quantitative bounds are proved in GenericSubspaceProbability;
orientation arguments can use the definition independently of that proof.
-/

section

open MaxCutGames.Gadget.Orientation

namespace MaxCutGames.Quadratic

/-- The actual uniform fraction of nongeneric rank-`r` binary subspaces. -/
def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end MaxCutGames.Quadratic
end

section

open scoped BigOperators Classical
open Module

namespace MaxCutGames.Gadget.FreshGenericity

open _root_.OAI.MaxCutGames.Gadget.Orientation Quadratic BlockDescent OrientedBlockKernel

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- A fixed coordinate equivalence transports the complete rank-indexed
Grassmannian bijectively, so it preserves its uniform distribution. -/
def rankSpaceEquiv (e : V ≃ₗ[K] W) (r : ℕ) : RankSpace K V r ≃ RankSpace K W r :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun S => by
    change finrank K S = r ↔ finrank K (S.map e.toLinearMap) = r
    rw [e.finrank_map_eq])

@[simp] theorem rankSpaceEquiv_apply (e : V ≃ₗ[K] W) (r : ℕ)
    (S : RankSpace K V r) :
    (rankSpaceEquiv e r S).val = S.val.map e.toLinearMap := rfl

local instance linearMapFintype [Fintype V] [Fintype W] : Fintype (V →ₗ[K] W) :=
  Fintype.ofInjective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective

local instance linearEquivFintype [Fintype V] [Fintype W] : Fintype (V ≃ₗ[K] W) :=
  Fintype.ofInjective (fun e : V ≃ₗ[K] W => (e : V → W)) DFunLike.coe_injective

local instance submoduleFintype [Fintype V] : Fintype (Submodule K V) :=
  Fintype.ofInjective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective

local instance rankSpaceFintype [Fintype V] (r : ℕ) : Fintype (RankSpace K V r) :=
  inferInstanceAs (Fintype {S : Submodule K V // finrank K S = r})

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Nongenericity includes the universal lift quantifier in `IsGeneric`.
The field's simultaneous bound includes rank zero as well. -/
def bad (S : Submodule (ZMod 2) (BinaryDual (F := F))) : Prop :=
  ¬ IsGeneric (traceSpace S)

theorem mean_bad_rankSpace (r : ℕ) :
    (𝔼 S : RankSpace (ZMod 2) (BinaryDual (F := F)) r,
      if bad S.val then (1 : ℚ) else 0) = nongenericFraction F r := by
  calc
    _ = 𝔼 S : RankSpace (ZMod 2) (Vec F) r,
        if ¬IsGeneric S.val then (1 : ℚ) else 0 := by
      exact Fintype.expect_equiv (rankSpaceEquiv traceDualEquiv.symm r) _ _
        (fun T => by
          by_cases h : IsGeneric (traceSpace T.val)
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_true_eq_false, ite_false]
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_false_eq_true, ite_true])
    _ = _ := by
      simp only [nongenericFraction, Fintype.expect_eq_sum_div_card,
        Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_fresh_bad_at_line
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) =
      nongenericFraction F
        (finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
          (lineGenerator A)).range) := by
  let E := (blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator A)).range
  calc
    _ = 𝔼 J : BlockOrientation A,
        if bad (E.map J.dualMap.toLinearMap) then (1 : ℚ) else 0 := by
      apply Finset.expect_congr rfl
      intro J _
      rw [childCharacter_range_eq_dual_pullback]
    _ = 𝔼 T : RankSpace (ZMod 2) (BinaryDual (F := F)) (finrank (ZMod 2) E),
        if bad T.val then (1 : ℚ) else 0 := by
      simp only [Fintype.expect_eq_sum_div_card]
      exact mean_dual_pullback E (chosenBlockOrientation A)
        (fun T => if bad T.val then (1 : ℚ) else 0)
    _ = _ := mean_bad_rankSpace _

omit [(A : FieldLine F) → Fintype (BlockOrientation A)] in

theorem unoriented_rank_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
      (lineGenerator A)).range ≤ finrank (ZMod 2) S := by
  calc
    _ ≤ finrank (ZMod 2) (traceSpace S) := LinearMap.finrank_range_le _
    _ = _ := traceSpace_finrank S

/-- The field error bound applies to the actual fresh descendant rank,
even though that rank depends on the earlier lift and the selected line. -/
theorem fresh_bad_at_line_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) ≤ ε := by
  rw [mean_fresh_bad_at_line]
  exact hgeneric _ ((unoriented_rank_le S γ A).trans hS)

variable [Fintype (FieldLine F)]

/-- Fresh nongenericity bound over the actual full child index.  The parent
family and the common-parent map are arbitrary fixed inputs, so the result
applies at every adaptive history without a future-lift independence premise. -/
theorem fresh_bad_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F))
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 i : BlockOrientationIndex F,
      if bad (childCharacter orientedBlockLinear γ i).range then (1 : ℚ) else 0) ≤ ε := by
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  calc
    _ ≤ 𝔼 _A : FieldLine F, ε := Finset.expect_le_expect
      (fun A _ => fresh_bad_at_line_le S γ A r₀ ε hS hgeneric)
    _ = ε := Fintype.expect_const _

/-- The fresh bound for the deterministic descendant of an actual parent
lift. The common-parent map is chosen from the whole lift before sampling the
child index, exactly as required by the adaptive finite-history experiment. -/
theorem descendant_bad_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J := orientedBlockLinear (F := F)
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S)
      (r₀ : ℕ) (ε : ℚ), finrank (ZMod 2) S ≤ r₀ →
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) →
      (𝔼 i : BlockOrientationIndex F,
        if bad (Descent.childDomain J hJ Q s S L i) then (1 : ℚ) else 0) ≤ ε := by
  intro J hJ Q s S L r₀ ε hS hgeneric
  simpa only [Descent.childDomain, J] using!
    fresh_bad_le S (Descent.commonGamma J hJ Q s S L) r₀ ε hS hgeneric

end MaxCutGames.Gadget.FreshGenericity
end

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

namespace MaxCutGames.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable instance noiseFintype (n : ℕ) : Fintype (Stage.iterate J hJ Q n).Noise := by
  induction n with
  | zero => exact Fintype.ofFinite B
  | succ n ih =>
    exact inferInstanceAs (Fintype (I × (Stage.iterate J hJ Q n).Noise))

noncomputable def terminalPotential (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  average (fun t => MaxCutGames.Gadget.Harmonic.harmonic (leafRank J hJ Q n S L t))

omit [FiniteDimensional k B] in
@[simp] theorem terminalPotential_zero (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    terminalPotential J hJ Q 0 S L = MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k S) := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k S)) = _
  exact average_const _

omit [FiniteDimensional k B] in
theorem terminalPotential_succ (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    terminalPotential J hJ Q (n + 1) S L =
      average (fun i => terminalPotential J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold terminalPotential average
  change Finset.univ.expect (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    MaxCutGames.Gadget.Harmonic.harmonic (leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- The only geometric inputs are the outgoing MaxCutGames.Gadget.Harmonic.harmonic loss estimate for
every lift and the fresh-orientation bound for every child image. The lift may
depend on every previous orientation; the proof never declares it independent. -/
theorem expected_terminal_loss
    (bad : Submodule k (B →ₗ[k] k) → Prop) [DecidablePred bad]
    (r₀ : ℕ) (C θ ε : ℚ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hsmall : C * ε ≤ 1)
    (hstep : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      average (fun i => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
        MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k (childDomain J hJ Q s S L i))) ≤
          3 * θ + C * θ * if bad S then 1 else 0)
    (hfresh : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      probability (fun i => bad (childDomain J hJ Q s S L i)) ≤ ε)
    (n : ℕ) (S : Submodule k (B →ₗ[k] k)) (L : Lift (Stage.iterate J hJ Q n) S)
    (hcap : Module.finrank k S ≤ r₀) :
    MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k S) - terminalPotential J hJ Q n S L ≤
      4 * n * θ + C * θ * if bad S then 1 else 0 := by
  induction n generalizing S with
  | zero =>
    simp only [terminalPotential_zero, sub_self, Nat.cast_zero, mul_zero, zero_mul,
      zero_add]
    split <;> simp_all [mul_nonneg]
  | succ n ih =>
    let s := Stage.iterate J hJ Q n
    let Sc := childDomain J hJ Q s S L
    let Lc := childLift J hJ Q s S L
    have hchild : average (fun i => MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k (Sc i)) -
        terminalPotential J hJ Q n (Sc i) (Lc i)) ≤
        4 * n * θ + C * θ * probability (fun i => bad (Sc i)) := by
      calc
        _ ≤ average (fun i => 4 * n * θ + C * θ * if bad (Sc i) then 1 else 0) := by
          apply average_mono
          intro i
          exact ih (Sc i) (Lc i) ((child_rank_le J hJ Q s S L i).trans hcap)
        _ = _ := by rw [average_add, average_const, average_mul_left]; rfl
    have hdrop := hstep s S L hcap
    have hbad := hfresh s S L hcap
    have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
    rw [terminalPotential_succ]
    rw [average_sub] at hchild
    rw [average_sub, average_const] at hdrop
    change MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
      average (fun i => terminalPotential J hJ Q n (Sc i) (Lc i)) ≤ _
    push_cast
    nlinarith

end MaxCutGames.Gadget.DescentProbability

namespace MaxCutGames.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def survivalProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  probability (fun t => 0 < leafRank J hJ Q n S L t)

noncomputable def detectionProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ := by
  classical
  exact probability (fun t => ∃ z : S, L.family z ((Stage.iterate J hJ Q n).noise t) ≠ 0)

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_nonneg (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    0 ≤ detectionProbability J hJ Q n S L := by
  classical
  exact probability_nonneg _

omit [FiniteDimensional (ZMod 2) B] in
/-- Restricting the logical domain can only remove detecting characters. -/
theorem detectionProbability_restrict_le (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T) :
    detectionProbability J hJ Q n S (L.restrict hST) ≤
      detectionProbability J hJ Q n T L := by
  classical
  apply probability_mono
  rintro t ⟨z, hz⟩
  exact ⟨Submodule.inclusion hST z, hz⟩

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_zero_of_rank_pos
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) (hrank : 0 < Module.finrank (ZMod 2) S) :
    (1 / 2 : ℚ) ≤ detectionProbability J hJ Q 0 S L := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨z, hz⟩ := exists_ne (0 : S)
  have hzval : z.val ≠ 0 := by
    intro he
    exact hz (Subtype.ext he)
  have hex : ∃ b : B, z.val b ≠ 0 := by
    by_contra h
    apply hzval
    ext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  have hagree : L.family z b = z.val b := L.agrees z b
  have hχ : L.family z b ≠ 0 := by rwa [hagree]
  change (1 / 2 : ℚ) ≤ probability (fun b : B => ∃ z : S, L.family z b ≠ 0)
  exact binary_family_detection_ge_half _ (L.family z).toAddMonoidHom b hχ
    (fun b hb => ⟨z, hb⟩)

omit [FiniteDimensional (ZMod 2) B] in
@[simp] theorem survivalProbability_zero
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    survivalProbability J hJ Q 0 S L =
      if 0 < Module.finrank (ZMod 2) S then 1 else 0 := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    if 0 < Module.finrank (ZMod 2) S then (1 : ℚ) else 0) = _
  exact average_const _

omit [FiniteDimensional (ZMod 2) B] in
theorem survivalProbability_succ (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    survivalProbability J hJ Q (n + 1) S L =
      average (fun i => survivalProbability J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold survivalProbability
  change probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    0 < leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2) = _
  exact probability_product _

omit [FiniteDimensional (ZMod 2) B] in
theorem average_child_detection_le (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    average (fun i => detectionProbability J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) ≤
        detectionProbability J hJ Q (n + 1) S L := by
  classical
  unfold detectionProbability
  change _ ≤ probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    ∃ z : S, L.family z ((Stage.iterate J hJ Q (n + 1)).noise t) ≠ 0)
  rw [probability_product]
  apply average_mono
  intro i
  apply probability_mono
  intro t hdetect
  exact child_detection J hJ Q (Stage.iterate J hJ Q n) S L i t hdetect

omit [FiniteDimensional (ZMod 2) B] in
/-- Detection by the root lift is at least one half the actual terminal-rank
survival probability, on precisely the recursively generated noise sample. -/
theorem half_survival_le_detection (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    (1 / 2 : ℚ) * survivalProbability J hJ Q n S L ≤
      detectionProbability J hJ Q n S L := by
  induction n generalizing S with
  | zero =>
    rw [survivalProbability_zero]
    split_ifs with hrank
    · simpa only [mul_one] using detectionProbability_zero_of_rank_pos J hJ Q S L hrank
    · simpa only [mul_zero] using detectionProbability_nonneg J hJ Q 0 S L
  | succ n ih =>
    rw [survivalProbability_succ, ← average_mul_left]
    calc
      _ ≤ average (fun i => detectionProbability J hJ Q n
          (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
          (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
        apply average_mono
        intro i
        exact ih _ _
      _ ≤ detectionProbability J hJ Q (n + 1) S L :=
        average_child_detection_le J hJ Q n S L

/-- Actual quarter detection follows from retaining half the initial
MaxCutGames.Gadget.Harmonic.harmonic potential; all leaf-to-root event containments are already proved. -/
theorem quarter_detection_of_terminal_potential (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S L) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n S L := by
  have hsurv : (1 / 2 : ℚ) ≤ survivalProbability J hJ Q n S L :=
    survival_probability_ge_half_of_potential (leafRank J hJ Q n S L)
      (Module.finrank (ZMod 2) S) hrank (leafRank_le J hJ Q n S L) hpotential
  have hdet := half_survival_le_detection J hJ Q n S L
  linarith

/-- The fixed generic top subspace may be chosen inside a full logical
family; the resulting quarter bound still concerns the original lift. -/
theorem quarter_detection_of_restricted_terminal_potential (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : MaxCutGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S (L.restrict hST)) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n T L :=
  (quarter_detection_of_terminal_potential J hJ Q n S (L.restrict hST)
    hrank hpotential).trans (detectionProbability_restrict_le J hJ Q n S T hST L)

end MaxCutGames.Gadget.LeafDetection

end

end OAI
