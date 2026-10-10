import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCompletionComparison
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCompletionLaws
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperIdealRejection
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentApproximation

namespace OAI

/-! # The implemented small walk and outer rejection have the three stated errors -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [FI : Fintype I] [FJ : Fintype J] [LI : LinearOrder I] [LJ : LinearOrder J]
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
local notation "μ" => finiteFibreLaw r c i₀ j₀ e b h hb a fallback
local notation "μB" => finiteBlockLaw r c i₀ j₀ e b h hb a fallback

def implementedSmallKernel (x : PaperStates r c) : RationalLaw (PaperStates r c) :=
  completionStepLaw R P (smallProposalLaw r c) μB x

local notation "Q" => implementedSmallKernel r c i₀ j₀ e b h hb a fallback

def implementedJointLaw (x : PaperStates r c) (n : ℕ) : RationalLaw (PaperStateJoint r c) :=
  dependentJointLaw (walkLaw Q x n) μ

variable [Nonempty (PaperStates r c)]
variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
variable (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q)
  (4*(dimensionAllowance (I := I) (J := J))^8)))

include hPL hCheeger

theorem implementedSmallKernel_variation (x : PaperStates r c) :
    variation (Q x) (smallTransitionLaw r c i₀ j₀ x) ≤ 1/(2:ℚ)^h := by
  have hv := @referenceStep_variation I J FI FJ LI LJ r c i₀ j₀ q e b h hb a fallback hPL hCheeger x
  have hs := congrArg (fun p : RationalLaw (PaperStates r c) => variation (Q x) p)
    (smallIdealStep_eq r c i₀ j₀ x)
  exact hs ▸ hv

/-- All adaptive transition errors and the independent terminal draw add
before rejection; the approximate kernel needs no stationarity claim. -/
theorem implementedJointLaw_variation (x : PaperStates r c) (n : ℕ) :
    (variation (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
      (stationaryJointLaw r c i₀ j₀):ℝ) ≤
    ((n:ℝ)+1)/(2:ℝ)^h+((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160) := by
  have hj := @finiteTerminalJoint_variation I J FI FJ LI LJ r c i₀ j₀ q e b h hb a fallback hPL hCheeger
    (walkLaw Q x n) (smallStationaryLaw r c i₀ j₀)
  have hw := walkLaw_variation Q (smallTransitionLaw r c i₀ j₀) (1/(2:ℚ)^h)
    (implementedSmallKernel_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger) x n
  have ht := variation_triangle (walkLaw Q x n) (smallWalkLaw r c i₀ j₀ x n)
    (smallStationaryLaw r c i₀ j₀)
  have hh : variation (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
      (stationaryJointLaw r c i₀ j₀) ≤
      ((n:ℚ)+1)*(1/(2:ℚ)^h)+variation (smallWalkLaw r c i₀ j₀ x n) (smallStationaryLaw r c i₀ j₀) := by
    change variation (walkLaw Q x n) (smallWalkLaw r c i₀ j₀ x n) ≤ _ at hw
    change variation (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
      (stationaryJointLaw r c i₀ j₀) ≤ _ at hj
    linarith
  have hhR := (Rat.cast_le (K := ℝ)).mpr hh
  simp only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,mul_one_div] at hhR
  exact hhR.trans (add_le_add_right (smallWalkLaw_variation r c i₀ j₀ x n) _)

/-- This is the manuscript's three-term bound for the actual finite
completion subroutine, ideal mixing, and first-success fallback. -/
theorem implementedOuterLaw_variation [Nonempty (Table r c)]
    (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    (variation (retryLaw (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
      (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(J₀:ℝ)/(2*(1+(d:ℝ)^2)))+
      (J₀:ℝ)*(((n:ℝ)+1)/(2:ℝ)^h+
        ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160)) := by
  have hr := retryLaw_variation (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n)
    (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀
  have ht := variation_triangle
    (retryLaw (implementedJointLaw r c i₀ j₀ e b h hb a fallback x n) (stateTrial r c) z₀ J₀)
    (retryLaw (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c))
  have hrR := (Rat.cast_le (K := ℝ)).mpr hr
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] at hrR htR
  have hj := mul_le_mul_of_nonneg_left
    (implementedJointLaw_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger x n)
    (show (0:ℝ) ≤ J₀ by positivity)
  have hi := ideal_outer_variation r c i₀ j₀ htotal z₀ J₀
  linarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
