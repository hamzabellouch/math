import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyMemo
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilySampling
import OAI.Combinatorics.EditApproximation.Probability.RejectionMemoCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilyEncoding
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Work

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)



 theorem physicalFamilyMemoBits_integrable (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (seed : SeedState) :
    Integrable (physicalFamilyMemoBits source target N P T S H hH bits encode rootQ seed)
      (rejectionRuntimeArrayLaw FamilyRange) := rejectionSelectedBits_integrable _ _

 theorem physicalFamilyMemoBits_expected_le (hH : 0 < H) (bits sourceBits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (seed : SeedState)
    (budget : ℝ)
    (hrequests : ∀ draw, ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ
      (seed, draw)).requests : ℝ) ≤ budget)
    (hbits : ∀ key, rejectionBitCount (FamilyRange key) ≤ sourceBits) :
    (∫ execution, physicalFamilyMemoBits source target N P T S H hH bits encode rootQ seed execution
      ∂rejectionRuntimeArrayLaw FamilyRange) ≤ 2 * (budget * sourceBits) := by
  classical
  let : Fintype Table := Fintype.ofInjective
    (fun key : Table => (⟨ChargedPhysicalRequest.code key,
      ChargedPhysicalRequest.code_bound (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) key⟩ :
        Fin (ChargedPhysicalRequest.capacity M J target.length (passes + 1) (H ^ 2) T S)))
    (fun _ _ h => ChargedPhysicalRequest.code_injective
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)) (congrArg Fin.val h))
  apply memo_rejectionBits_expected_le_real FamilyRange _ budget sourceBits _ hbits
  intro draw
  have hf : (physicalFamilyMemoResult source target N P T S H hH bits encode rootQ
      (seed, draw)).freshKeys.length ≤
      (physicalFamilyMemoResult source target N P T S H hH bits encode rootQ (seed, draw)).requests :=
    (rankedMemoEvaluate_resource_bounds _ _ _ _ _ _).1
  exact (Nat.cast_le (α := ℝ)).mpr hf |>.trans (hrequests draw)

 theorem physicalFamilyMemo_nodes_polynomial (hH : 0 < H)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length)
    (input : SeedState × PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) :
    (physicalFamilyMemoResult source target N P T S H hH (16384 * inputHeight N + 5)
      encode rootQ input).memory.nodes + 1 ≤ (N + 2) ^ 65542 :=
  computed_mixed_cache_nodes N _ _ encode _

end Work

end EditApproximation

end OAI
