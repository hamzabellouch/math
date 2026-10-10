import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyTrace
import OAI.Combinatorics.EditApproximation.Geometry.LocalCommonTrace

namespace OAI

namespace EditApproximation

section SourceFamily

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H passes : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

variable (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P (inputSmallLog N) (40 * smallLogExponent N) H ((inputSmallLog N) ^ 80) passes (H ^ 2))


noncomputable def physicalFamilyPrefix (seed : SeedState) (n : ℕ) (hn : n ≤ passes) :
    LocalCommonTrace (M := M) (J := J) (R := R) target N P H n :=
  let rows : Fin n → LocalCommonDraw (M := M) (J := J) (R := R) target N P H :=
    fun p copy => physicalFamilyPack (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw
      ⟨p.val, Nat.lt_succ_of_le (p.isLt.le.trans hn)⟩ copy.castSucc
  commonArrayToTrace (Seed := SeedState)
    (Ω := LocalCommonDraw (M := M) (J := J) (R := R) target N P H) n (seed, rows)


omit [DecidableEq α] [NeZero M] [NeZero R] in
 theorem physicalFamilyDraw_fin (pass : Fin (passes + 1)) (copy : Fin (H ^ 2 + 1)) :
    physicalFamilyDraw (M := M) (J := J) (R := R) target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw pass.val copy.val =
      physicalFamilyCurry (M := M) (J := J) (R := R) target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw pass copy := by
  funext key
  unfold physicalFamilyDraw physicalFamilyCurry
  have hp : Fin.ofNat (passes + 1) pass.val = pass := Fin.ext (Nat.mod_eq_of_lt pass.isLt)
  have hc : Fin.ofNat (H ^ 2 + 1) copy.val = copy := Fin.ext (Nat.mod_eq_of_lt copy.isLt)
  rw [hp, hc]


omit [DecidableEq α] [NeZero M] [NeZero R] in
 theorem physicalFamilyPrefix_succ (seed : SeedState) (n : ℕ) (hn : n + 1 ≤ passes) :
    physicalFamilyPrefix target N P H passes draw seed (n + 1) hn =
      (physicalFamilyPrefix target N P H passes draw seed n (by omega),
        fun copy : Fin (H ^ 2) => physicalFamilyPack (M := M) (J := J) (R := R) target N P ell exponent H (ell ^ 80)
          passes (H ^ 2) draw ⟨n, by omega⟩ copy.castSucc) := rfl


omit [DecidableEq α] [NeZero M] [NeZero R] in
 theorem physicalFamilyToTrace_fst (seed : SeedState) :
    (physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2)
      (seed, draw)).1 = physicalFamilyPrefix target N P H passes draw seed passes le_rfl := by
  unfold physicalFamilyToTrace commonArrayFinal
  dsimp only
  rw [mapCommonTrace_array]
  rfl


omit [DecidableEq α] [NeZero M] [NeZero R] in
 theorem physicalFamilyToTrace_snd (seed : SeedState) :
    (physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2)
      (seed, draw)).2 =
    physicalFamilyPack (M := M) (J := J) (R := R) target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw
      (Fin.last passes) 0 := rfl


omit [NeZero M] [NeZero R] in
 theorem physicalFamilySample_fin
    (seed : SeedState) (pass : Fin (passes + 1)) (copy : Fin (H ^ 2 + 1)) :
    physicalFamilySample source target N P ell exponent H (ell ^ 80) T passes (H ^ 2)
      (scheduledSeedFactor N) tau hP draw (clampedSeedNat seed) pass.val copy.val =
    physicalCommonSample source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N pass.val) T exponent H (ell ^ 80) R
      (localOnlineMassBound M P H) tau
      (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
        (scheduledSeedFactor N pass.val) T exponent H tau hP)
      (physicalFamilyPack (M := M) (J := J) (R := R) target N P ell exponent H (ell ^ 80) passes (H ^ 2) draw pass copy) := by
  unfold physicalFamilySample physicalFamilyPack
  rw [physicalFamilyDraw_fin]


 theorem localScheduledSeedNext_nat_value (pass : ℕ) (previous : SeedState)
    (samples : LocalScheduledSeedDraw (R := R) source target N P T H pass previous) :
    clampedSeedNat (localScheduledSeedNext source target N P T S H pass previous samples) =
      fun state => min N (upperMedian (List.ofFn fun copy : Fin (H ^ 2) =>
        ⌈(scheduledSeedMultiplier N pass : ℚ) * physicalLocalJointValue source target
          (clampedSeedNat previous) N P ell (scheduledSeedFactor N pass) T exponent H (ell ^ 80)
          tau eta kappa delta (samples copy) state.1 S state.2⌉₊)) := rfl


 theorem physicalFamilySeed_prefix [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (seed : SeedState) : ∀ (n : ℕ) (hn : n ≤ passes),
    physicalFamilySeed source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP draw
      (clampedSeedNat seed) n =
    clampedSeedNat (localCommonSeed source target N P T S H hP n
      (physicalFamilyPrefix target N P H passes draw seed n hn)) := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
    intro hn
    let previous := localCommonSeed source target N P T S H hP n
      (physicalFamilyPrefix target N P H passes draw seed n (by omega))
    let row := fun copy : Fin (H ^ 2) => physicalFamilyPack (M := M) (J := J) (R := R) target N P ell exponent H
      (ell ^ 80) passes (H ^ 2) draw ⟨n, by omega⟩ copy.castSucc
    have hnext : localCommonSeed source target N P T S H hP (n + 1)
        (physicalFamilyPrefix target N P H passes draw seed (n + 1) hn) =
        localScheduledSeedNext source target N P T S H n previous
          (localCommonSample source target N P T H hP n previous row) := rfl
    have hsamples :
        (fun copy : Fin (H ^ 2) => physicalFamilySample source target N P ell exponent H
          (ell ^ 80) T passes (H ^ 2) (scheduledSeedFactor N) tau hP draw
          (clampedSeedNat previous) n copy.val) =
        localCommonSample source target N P T H hP n previous row := by
      funext copy
      exact physicalFamilySample_fin source target N P T H passes hP draw previous
        ⟨n, by omega⟩ copy.castSucc
    rw [hnext, localScheduledSeedNext_nat_value, physicalFamilySeed, ih (by omega)]
    rw [← hsamples]

end SourceFamily

end EditApproximation

end OAI
