import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperIdealKernel
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentApproximation

namespace OAI

/-! # Completion approximation through the fixed fibre equivalence -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
variable (a : GridBoundary.Grid (I := Fin q) (4*(dimensionAllowance (I := I) (J := J))^8))
variable (fallback : (z : PaperStates r c) → PaperFibre r c z)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀
local notation "μB" => finiteBlockLaw r c i₀ j₀ e b h hb a fallback

theorem finiteReferenceLaw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (z : PaperStates r c) :
    variation (μB z) (idealReferenceLaw r c i₀ j₀ z) ≤ 1/(2:ℚ)^h := by
  unfold finiteBlockLaw idealReferenceLaw
  rw [variation_equiv]
  exact finiteFibreLaw_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger z

theorem referenceStep_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (x : PaperStates r c) :
    variation (completionStepLaw R P (smallProposalLaw r c) μB x)
      (completionStepLaw R P (smallProposalLaw r c) (idealReferenceLaw r c i₀ j₀) x) ≤
      1/(2:ℚ)^h := by
  apply completionStep_variation
  intro z
  exact finiteReferenceLaw_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger z

theorem finiteTerminalJoint_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (p q' : RationalLaw (PaperStates r c)) :
    variation (dependentJointLaw p (finiteFibreLaw r c i₀ j₀ e b h hb a fallback))
      (dependentJointLaw q' (fun z => uniformLaw (α := PaperFibre r c z))) ≤
      variation p q'+1/(2:ℚ)^h := by
  apply variation_dependentJoint_uniform
  intro z
  exact finiteFibreLaw_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger z

end
end ContingencyTables.SmallGraphProfiles

end OAI
