import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCommonSource
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineMassBound
import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSchedule
import OAI.Combinatorics.EditApproximation.Geometry.CommonSeedTrace

namespace OAI

/-! Concrete common-source seed passes. The sampler range cap is proved
for every seed; no good-seed event is used to define or bound the draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CommonSeed

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

abbrev LocalCommonDraw := Fin (H ^ 2) →
  PhysicalCommonDraw M J N target.length thetaExponent ell (ell ^ 80) R cap

noncomputable def localCommonDrawLaw :
    Measure (LocalCommonDraw (M := M) (J := J) (R := R) target N P H) :=
  Measure.pi fun _ : Fin (H ^ 2) =>
    physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap

instance localCommonDrawLaw_probability : IsProbabilityMeasure
    (localCommonDrawLaw (M := M) (J := J) (R := R) target N P H) := by
  unfold localCommonDrawLaw
  infer_instance

noncomputable def localCommonSample (hP : 0 < P) (pass : ℕ) (seed : Seed)
    (draw : LocalCommonDraw (M := M) (J := J) (R := R) target N P H) :
    LocalScheduledSeedDraw (R := R) source target N P T H pass seed :=
  fun copy => physicalCommonSample source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N pass) T thetaExponent H tau hP) (draw copy)

omit [NeZero R] in
theorem localCommonSample_law (hP : 0 < P) (pass : ℕ) (seed : Seed) :
    (localCommonDrawLaw (M := M) (J := J) (R := R) target N P H).map
        (localCommonSample source target N P T H hP pass seed) =
      localScheduledSeedDrawLaw (R := R) source target N P T H pass seed := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin (H ^ 2) =>
    physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap)
    (fun _ => (measurable_of_finite
      (physicalCommonSample source target (clampedSeedNat seed) N P ell
        (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
        (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
          (scheduledSeedFactor N pass) T thetaExponent H tau hP))).aemeasurable)
  refine h.trans ?_
  congr 1
  funext copy
  exact physicalCommonSample_law source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N pass) T thetaExponent H tau hP)

abbrev LocalCommonTrace (passes : ℕ) := CommonSeedTrace Seed
  (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

noncomputable instance localCommonTraceFintype (passes : ℕ) :
    Fintype (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) := by
  classical
  exact commonSeedTraceFintype Seed
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

instance localCommonTraceSingleton (passes : ℕ) :
    MeasurableSingletonClass
      (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) := by
  exact commonSeedTraceSingleton Seed
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

noncomputable def localCommonSeed (hP : 0 < P) (passes : ℕ)
    (trace : LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) : Seed :=
  commonTraceValue (localCommonSample source target N P T H hP)
    (localScheduledSeedNext (R := R) source target N P T S H) passes trace

noncomputable def localCommonTraceLaw (incoming : Measure Seed) (passes : ℕ) :
    Measure (LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes) :=
  commonTraceLaw (fun _ => localCommonDrawLaw (M := M) (J := J) (R := R) target N P H) incoming passes

instance localCommonTraceLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) : IsProbabilityMeasure
      (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes) := by
  classical
  unfold localCommonTraceLaw
  infer_instance

theorem localCommonSeed_law (hP : 0 < P) (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) :
    (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes).map
        (localCommonSeed source target N P T S H hP passes) =
      localScheduledSeedLaw (R := R) source target N P T S H incoming passes := by
  classical
  exact commonTraceLaw_map (localScheduledSeedDrawLaw (R := R) source target N P T H)
    (fun _ => localCommonDrawLaw (M := M) (J := J) (R := R) target N P H)
    (localCommonSample source target N P T H hP)
    (localScheduledSeedNext (R := R) source target N P T S H) incoming
    (localCommonSample_law source target N P T H hP) passes

end CommonSeed

end EditApproximation

end OAI
