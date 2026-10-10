import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionCount

namespace OAI

/-! # Computing the dense cache and the unused-bit multiplicity -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] residualParameters residualParametersRealizer canonicalBitCount
  canonicalBitCountRealizer completionWeights completionWeightsRealizer

abbrev TransitionCacheParameters := ResidualParameters×ℕ

def completionMultiplicity (z : TransitionCacheParameters) : ℕ :=
  BinaryPowerPrograms.power (2,z.2-canonicalBitCount (residualParameters z.1))

def completionMultiplicityRealizer : Realizer completionMultiplicity := by
  let used : Realizer (fun z : TransitionCacheParameters =>
      canonicalBitCount (residualParameters z.1)) :=
    composition (f := fun z : TransitionCacheParameters => residualParameters z.1)
      (g := canonicalBitCount)
      (composition (f := fun z : TransitionCacheParameters => z.1) (g := residualParameters)
        first residualParametersRealizer) canonicalBitCountRealizer
  let remaining : Realizer (fun z : TransitionCacheParameters =>
      z.2-canonicalBitCount (residualParameters z.1)) :=
    composition (f := fun z : TransitionCacheParameters =>
      (z.2,canonicalBitCount (residualParameters z.1)))
      (g := fun z : ℕ×ℕ => z.1-z.2) (pair second used) subtract
  exact composition (f := fun z : TransitionCacheParameters =>
      (2,z.2-canonicalBitCount (residualParameters z.1))) (g := BinaryPowerPrograms.power)
    (pair (constant 2) remaining) BinaryPowerPrograms.powerRealizer

def prepareTransitionCache (z : TransitionCacheParameters) : TransitionCache :=
  (z.1,(completionMultiplicity z,completionWeights (residualParameters z.1)))

def prepareTransitionCacheRealizer : Realizer prepareTransitionCache :=
  pair first (pair completionMultiplicityRealizer
    (composition (f := fun z : TransitionCacheParameters => residualParameters z.1)
      (g := completionWeights)
      (composition (f := fun z : TransitionCacheParameters => z.1) (g := residualParameters)
        first residualParametersRealizer) completionWeightsRealizer))

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

lemma completionMultiplicity_encoded (b h : ℕ) (x : PaperStates r c) :
    completionMultiplicity ((((stateCodeData r c e x,d^12),(d,h)),25*(d+b+h+1)^62))=
      2^(25*(d+b+h+1)^62-normalizedDrawBits (R x) (P x) d h) := by
  unfold completionMultiplicity
  rw [residualParameters_code r c hr hc e,BinaryPowerPrograms.power_eq,
    canonicalBitCount_code (R x) (P x) (by have := listed_dimension_fourteen r c hr hc; omega)
      (listed_paper_totals r c hr hc x)]

lemma prepareTransitionCache_encoded (b h : ℕ) (x : PaperStates r c) :
    prepareTransitionCache ((((stateCodeData r c e x,d^12),(d,h)),25*(d+b+h+1)^62))=
      (((stateCodeData r c e x,d^12),(d,h)),
        (2^(25*(d+b+h+1)^62-normalizedDrawBits (R x) (P x) d h),
          completionWeights ((marginCode (R x),marginCode (P x)),(d,h)))) := by
  unfold prepareTransitionCache
  rw [completionMultiplicity_encoded r c e hr hc,
    residualParameters_code r c hr hc e]

end
end ContingencyTables.SmallGraphProfiles

end OAI
