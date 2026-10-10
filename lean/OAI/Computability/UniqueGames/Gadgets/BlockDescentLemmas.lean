import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Computability.UniqueGames.Gadgets.OrientedBlockKernel
import OAI.Computability.UniqueGames.Gadgets.QuotientLemmas
import OAI.Computability.UniqueGames.Quadratic.GenericSeparationLemmas
import OAI.Computability.UniqueGames.Quadratic.HarmonicLoss
import OAI.Computability.UniqueGames.Quadratic.OrientedRestrictionLemmas
import OAI.Computability.UniqueGames.Quadratic.TraceDual

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Gadget.BlockDescent

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

end Gadget.BlockDescent

namespace Gadget.FreshGenericity

open scoped BigOperators Classical
open Module

open Orientation Quadratic BlockDescent OrientedBlockKernel

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

omit [∀ A : FieldLine F, Fintype (BlockOrientation A)] in
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
  simpa only [Descent.childDomain] using!
    fresh_bad_le S (Descent.commonGamma J hJ Q s S L) r₀ ε hS hgeneric

end Gadget.FreshGenericity

/-!
# Outgoing harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

namespace Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
local instance : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) := Fintype.ofFinite _

def outgoingLoss (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : ℚ :=
  average (fun i : BlockOrientationIndex F => harmonic (Module.finrank (ZMod 2) S) -
    harmonic (Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ i).range))

/-- Averaging all binary orientations reduces exactly to the actual line-law
rank experiment, after transporting logical characters by the trace pairing. -/
theorem outgoingLoss_eq_line_average
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ = average (fun A : FieldLine F =>
      harmonic (Module.finrank (ZMod 2) S) -
        harmonic (nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A)) := by
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

/-- Nongeneric actual child maps satisfy the fallback harmonic charge. -/
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
      average (fun i : BlockOrientationIndex F => harmonic (Module.finrank (ZMod 2) S) -
        harmonic (Module.finrank (ZMod 2) (Descent.childDomain J hJ Q s S L i))) ≤
        3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F *
          if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  intro J hJ Q s S L r₀ hcap hdec
  exact outgoing_harmonic_loss_le S (Descent.commonGamma J hJ Q s S L) r₀ hcap

end Gadget.OutgoingHarmonic

namespace Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

/-- Turn the fixed generic vector subspace into its actual logical characters. -/
def logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    Submodule (ZMod 2) (BinaryDual (F := F)) :=
  S.map traceDualEquiv.toLinearMap

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem traceSpace_logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    traceSpace (logicalCharacters S) = S := by
  exact (Submodule.map_symm_eq_iff traceDualEquiv).mpr rfl

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem logicalCharacters_finrank (S : Submodule (ZMod 2) (Vec F)) :
    Module.finrank (ZMod 2) (logicalCharacters S) = Module.finrank (ZMod 2) S :=
  traceDualEquiv.finrank_map_eq S

omit [CharP F 2] [Algebra (ZMod 2) F] [DecidableEq (BlockOrientationIndex F)]
    [Nonempty (BlockOrientationIndex F)] in
theorem theta_pos : 0 < fieldLineTheta F := by
  have hc : (0 : ℚ) < Nat.card (FieldLine F) := by
    exact_mod_cast (card_FieldLine_pos (F := F))
  exact inv_pos.mpr hc
/-- All probabilities concern the actual recursive noise choices. The field
and generic top space satisfy separately proved finite-field properties; no
probability estimate for the whole recursive gadget is an input. -/
theorem full_lift_detection :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (r₀ : ℕ) (ε : ℚ) (_hr₀ : 0 < r₀)
      (_hbudget : badRankCoefficient r₀ * ε ≤ 1)
      (_hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
      (S₀ : Submodule (ZMod 2) (Vec F))
      (_hrank : Module.finrank (ZMod 2) S₀ = r₀) (_hS₀ : IsGeneric S₀)
      (L : Lift (Stage.iterate J hJ Q (depth r₀ (fieldLineTheta F)))
        (⊤ : Submodule (ZMod 2) (BinaryDual (F := F)))),
      (1 / 4 : ℚ) ≤ detectionProbability J hJ Q
        (depth r₀ (fieldLineTheta F)) ⊤ L := by
  intro J hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  classical
  let S := logicalCharacters S₀
  have hSrank : Module.finrank (ZMod 2) S = r₀ :=
    (logicalCharacters_finrank S₀).trans hrank
  have hSgeneric : IsGeneric (traceSpace S) := by
    simpa only [S, traceSpace_logicalCharacters] using hS₀
  let L₀ := L.restrict (show S ≤ ⊤ from le_top)
  have hdrop := DescentProbability.expected_terminal_loss J hJ Q
    (fun T => ¬ IsGeneric (traceSpace T)) r₀ (badRankCoefficient r₀)
    (fieldLineTheta F) ε (badRankCoefficient_nonneg r₀) (le_of_lt theta_pos) hbudget
    (by
      intro s T L' hT
      exact OutgoingHarmonic.descendant_harmonic_loss_le hJ Q s T L' r₀ hT)
    (by
      intro s T L' hT
      have hf := FreshGenericity.descendant_bad_le hJ Q s T L' r₀ ε hT hgeneric
      refine (le_of_eq ?_).trans hf
      apply Finset.expect_congr rfl
      intro i _
      by_cases hi : IsGeneric (traceSpace (childDomain J hJ Q s T L' i))
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_true_eq_false, ite_false]
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_false_eq_true, ite_true])
    (depth r₀ (fieldLineTheta F)) S L₀ hSrank.le
  have hdepth := depth_budget r₀ (fieldLineTheta F) theta_pos
  have hpotential : harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q (depth r₀ (fieldLineTheta F)) S L₀ := by
    simp only [hSgeneric, not_true_eq_false, ite_false, mul_zero, add_zero, hSrank] at hdrop ⊢
    linarith
  exact quarter_detection_of_restricted_terminal_potential J hJ Q
    (depth r₀ (fieldLineTheta F)) S ⊤ le_top L (hSrank.symm ▸ hr₀) hpotential

end Gadget.BaseDetection

end UniqueGamesTheorem

end

end OAI
