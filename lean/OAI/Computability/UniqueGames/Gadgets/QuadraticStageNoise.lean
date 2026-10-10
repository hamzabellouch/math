import OAI.Computability.UniqueGames.Gadgets.NonlinearRecurrenceLemmas
import OAI.Computability.UniqueGames.Gadgets.OrientedBlockKernel
import OAI.Computability.UniqueGames.Quadratic.BlockKernelLemmas

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance automorphismFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
noncomputable local instance automorphismFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Fintype.ofFinite _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

theorem actual_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      NonlinearRecurrence.change (fun z => z.2 + Q z.1) p (blockEmbedding i d)) =
      rate F := by
  classical
  exact OrientedBlockKernel.mean_oriented_block_kernel d hd

/-- The actual recursive spaces, shifts, outputs and finite leaf-noise sampler. -/
noncomputable def stage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  Stage.iterate (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n

theorem stage_error (n : ℕ) :
    StageNoiseRecurrence.error (stage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  have he := StageNoiseRecurrence.iterate_error (blockEmbedding (F := F))
    aggregate_blockEmbedding_surjective Q (rate F) actual_kernel n
  simpa only [stage, Vec, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.card_eq_fintype_card] using he

/-- The logical alphabet is an actual injected shift subspace after quotient. -/
noncomputable def quotientStage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  StageQuotient.toStage (stage (F := F) n)

theorem quotientStage_error (n : ℕ) :
    StageNoiseRecurrence.error (quotientStage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  rw [quotientStage, StageNoiseRecurrence.quotient_error, stage_error]

end UniqueGamesTheorem.Gadget.QuadraticStageNoise

end

end

end OAI
