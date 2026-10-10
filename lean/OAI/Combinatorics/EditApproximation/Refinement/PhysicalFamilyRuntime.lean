import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyAccuracy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilySampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The source family is the projection of terminating rejection-sampling executions. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Runtime

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



noncomputable def physicalFamilyRuntimeLaw (incoming : Measure SeedState) :
    Measure (PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H) :=
  incoming.prod (rejectionRuntimeArrayLaw FamilyRange)

instance physicalFamilyRuntimeLaw_probability (incoming : Measure SeedState)
    [IsProbabilityMeasure incoming] :
    IsProbabilityMeasure (physicalFamilyRuntimeLaw (R := R) target N P H incoming) := by
  unfold physicalFamilyRuntimeLaw
  infer_instance



omit [DecidableEq α] [NeZero R] in
 theorem physicalFamilyRuntimeAccepted_law (incoming : Measure SeedState) [IsProbabilityMeasure incoming] :
    (physicalFamilyRuntimeLaw (R := R) target N P H incoming).map
      (physicalFamilyRuntimeAccepted (R := R) target N P H) =
    incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) := by
  change (incoming.prod (rejectionRuntimeArrayLaw FamilyRange)).map
    (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    physicalFamily_rejection_runtime_law]

noncomputable def physicalFamilyRuntimeAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) Table → ℕ)
    (rootQ : TargetInterval target.length)
    (execution : PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ
    (physicalFamilyRuntimeAccepted target N P H execution)

 theorem physicalFamilyRuntimeAnswer_event (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (incoming : Measure SeedState) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (physicalFamilyRuntimeLaw (R := R) target N P H incoming).real
      {execution | physicalFamilyRuntimeAnswer source target N P T S H hH bits encode rootQ execution ∈ event} =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {input | localFinalProgramAnswer (R := R) source target N P T S H rootQ input ∈ event} := by
  rw [← physicalFamilyMemoAnswer_event source target N P T S H hP hH bits encode hinjective hbounded
    incoming rootQ event, ← physicalFamilyRuntimeAccepted_law target N P H incoming,
    map_measureReal_apply (by unfold physicalFamilyRuntimeAccepted; fun_prop) (by exact (Set.toFinite _).measurableSet)]
  rfl

end Runtime

end EditApproximation

end OAI
