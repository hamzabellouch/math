import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Gadgets.BlockDescentLemmas
import OAI.Computability.UniqueGames.Gadgets.NonlinearRecurrenceLemmas
import OAI.Computability.UniqueGames.Gadgets.QuadraticStageNoise
import OAI.Computability.UniqueGames.Quadratic.GenericFieldChoice

namespace OAI

section

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

namespace UniqueGamesTheorem.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem theta_le_one : fieldLineTheta F ≤ 1 := by
  have hc : (1 : ℚ) ≤ Nat.card (FieldLine F) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_FieldLine_pos (F := F)))
  exact (inv_anti₀ (by norm_num : (0 : ℚ) < 1) hc).trans_eq (by norm_num)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rate_eq_one_sub_theta : rate F = 1 - fieldLineTheta F := by
  rw [rate, fieldLineTheta_eq, one_div]

/-- Detection for the actual quotient, with every whole-recursion estimate
discharged by the adaptive harmonic argument. -/
theorem quotient_detection
    (r₀ : ℕ) (ε : ℚ) (hr₀ : 0 < r₀)
    (hbudget : badRankCoefficient r₀ * ε ≤ 1)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
    (S₀ : Submodule (ZMod 2) (Vec F))
    (hrank : Module.finrank (ZMod 2) S₀ = r₀) (hS₀ : IsGeneric S₀)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (T : (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).Input →ₗ[ZMod 2] E)
    (hinj : Function.Injective
      (T.comp (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).embed)) :
    (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
      if T ((quotientStage (F := F) (depth r₀ (fieldLineTheta F))).noise t) ≠ 0
      then 1 else 0) := by
  classical
  let n := depth r₀ (fieldLineTheta F)
  let : Fintype (stage (F := F) n).Noise := DescentProbability.noiseFintype
    (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n
  have hJ : Function.Surjective
      (aggregate (OrientedBlockKernel.orientedBlockLinear (F := F))) := by
    exact aggregate_blockEmbedding_surjective (F := F)
  have hfull : ∀ L : Lift (stage (F := F) n)
      (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Vec F))),
      (1 / 4 : ℚ) ≤ probability (fun t => ∃ z, L.family z ((stage n).noise t) ≠ 0) := by
    intro L
    exact BaseDetection.full_lift_detection hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  have h := QuotientDetection.target_detection_after_quotient
    (stage (F := F) n) T (1 / 4) hfull hinj
  change (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average
    (fun t : (stage (F := F) n).Noise =>
      if T (StageQuotient.noise (stage (F := F) n) t) ≠ 0 then 1 else 0)
  rw [StageNoiseRecurrence.average_eq_expect]
  exact h

/-- The exact nonlinear recurrence satisfies the scalar budget fixed before
the field was selected. -/
theorem quotient_error_le (p : ℚ) (r₀ : ℕ)
    (hgeom : (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) ≤ p) :
    StageNoiseRecurrence.error
      (quotientStage (F := F) (depth r₀ (fieldLineTheta F))) ≤ p := by
  rw [quotientStage_error, rate_eq_one_sub_theta]
  have hpow : 0 ≤ (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) :=
    pow_nonneg (sub_nonneg.mpr theta_le_one) _
  have hcoef : 1 - 1 / (Nat.card F : ℚ) ^ 3 ≤ 1 :=
    sub_le_self _ (by positivity)
  exact (mul_le_of_le_one_left hpow hcoef).trans hgeom

/-- The unconditional finite base endpoint. All choices depend only on `p`;
the larger logical alphabet used by the final enlargement is absent here. -/
theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  obtain ⟨r₀, ε, hr₀, hε, _hεone, hbudget, hgeom⟩ := effective_parameters p hp
  obtain ⟨d, hd, _hdim, hgeneric, S₀, hS₀⟩ :=
    exists_uniform_generic_field r₀ ε hε
  refine ⟨d, hd, depth r₀ (fieldLineTheta (BinaryField d)), ?_, ?_⟩
  · exact quotient_error_le p r₀
      (hgeom _ BaseDetection.theta_pos theta_le_one)
  · intro E _ _ T hinj
    exact quotient_detection r₀ ε hr₀ hbudget hgeneric S₀.1 S₀.2 hS₀ T hinj

end

end UniqueGamesTheorem.Gadget.BaseConstruction

end

end OAI
