import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma profile_combined_mask (R T seed : Ideal O) (ν : ι→Ideal O→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v *
      idealMask (idealGenerator T) (finiteTupleProduct v) =
    profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  rw [idealMask_generator]
  simp only [profileCoefficient, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

lemma column_combined_mask (S : Finset (Tuple ι)) (R T seed : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    maskedSource (idealGenerator T)
      (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)) =
    finiteColumnCoefficient S (profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) := by
  funext I
  unfold maskedSource finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [←(Finset.mem_filter.mp hv).2]
  exact profile_combined_mask R T seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (idealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma extracted_input (s : Input ι) (η : Character) (R T seed C : Ideal O)
    (hC : Supported C) (t : ℝ) (I : Ideal O) :
    extractedSource η (idealGenerator T) C (original s R seed).beta t I =
      (original s (R*T) seed).beta (C*I) * rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource_whole_mask η (idealGenerator T) C hC, input_combined_mask]
  rfl

theorem extracted_input_allocations (s : Input ι) (η τ : Character)
    (R T seed C I : Ideal O) (hC : Supported C) (hI : I≠0)
    (hseed : IsCoprime seed C) (t : ℝ) :
    (if IsCoprime C I then
      extractedSource η (idealGenerator T) C (original s R seed).beta t I else 0) =
    rowWeight η fixedBadMask 1 1 t C *
      ∑ B : actualAllocations s.pools C,
        frozenCoefficient B C (R*T) s.ν s.W s.P *
          (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta I := by
  have hh := original_masked_live_column s.pools s.pools_ne
    (fun i J hJ => s.prime i J hJ) C (R*T) seed I hC.1 hI hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  rw [extracted_input s η R T seed C hC t I]
  calc
    _ = rowWeight η fixedBadMask 1 1 t C *
        (if IsCoprime C I then (original s (R*T) seed).beta (C*I) else 0) := by
      split_ifs <;> ring
    _ = rowWeight η fixedBadMask 1 1 t C *
        ∑ B : actualAllocations s.pools C, frozenCoefficient B C (R*T) s.ν s.W s.P *
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C (R*T) seed s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I := by
      exact congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z) hh
    _ = _ := by
      apply congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z)
      apply Finset.sum_congr rfl
      intro B _
      exact congrArg (fun z : ℂ => frozenCoefficient B C (R*T) s.ν s.W s.P * z)
        (congrFun (child_columns s C (R*T) seed B τ t).2 I)

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (idealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    maskedSource (idealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI
