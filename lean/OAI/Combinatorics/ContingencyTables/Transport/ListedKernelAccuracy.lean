import OAI.Combinatorics.ContingencyTables.Transport.ListedReservedDraw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperImplementedLaw

namespace OAI

/-! # Mixing with the computed, canonically initialized completion draw -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits CompletionTranslation CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "i₀" => largeOptionEquiv r (d^20) hr none
local notation "j₀" => largeOptionEquiv c (d^20) hc none
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

def listedFibreLaw (z : PaperStates r c) : RationalLaw (PaperFibre r c z) :=
  mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool)) (listedPaddedDraw r c hr hc b h hb z)

def listedReferenceLaw (z : PaperStates r c) : RationalLaw (Table (R z) (P z)) :=
  equivLaw (paperReferenceEquiv r c i₀ j₀ z) (listedFibreLaw r c hr hc b h hb z)

def listedSmallKernel (z : PaperStates r c) : RationalLaw (PaperStates r c) :=
  completionStepLaw R P (smallProposalLaw r c) (listedReferenceLaw r c hr hc b h hb) z

def listedJointLaw (x : PaperStates r c) (steps : ℕ) : RationalLaw (PaperStateJoint r c) :=
  dependentJointLaw (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
    (listedFibreLaw r c hr hc b h hb)

variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
  (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
variable (hCheeger : PublishedInputs.FiniteCheeger
  (GridBoundary.Grid (I := Fin (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
    (4*(dimensionAllowance (I := Fin m) (J := Fin n))^8)))

include hPL hCheeger


theorem listedFibreLaw_variation (z : PaperStates r c) :
    variation (listedFibreLaw r c hr hc b h hb z) (uniformLaw (α := PaperFibre r c z)) ≤ 1/(2:ℚ)^h := by
  have ht := @listedDenseDraw_variation m n r c hr hc
    hPL hCheeger h z
  rw [←listedPaddedDraw_law r c hr hc b h hb z] at ht
  change (variation (listedFibreLaw r c hr hc b h hb z)
    (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ _ at ht
  rw [←dyadicError_cast] at ht
  exact (Rat.cast_le (K := ℝ)).mp ht

theorem listedReferenceLaw_variation (z : PaperStates r c) :
    variation (listedReferenceLaw r c hr hc b h hb z) (idealReferenceLaw r c i₀ j₀ z) ≤ 1/(2:ℚ)^h := by
  unfold listedReferenceLaw idealReferenceLaw
  rw [variation_equiv]
  exact listedFibreLaw_variation r c hr hc b h hb hPL hCheeger z

variable [Nonempty (PaperStates r c)]

theorem listedSmallKernel_variation (x : PaperStates r c) :
    variation (listedSmallKernel r c hr hc b h hb x) (smallTransitionLaw r c i₀ j₀ x) ≤ 1/(2:ℚ)^h := by
  rw [←smallIdealStep_eq r c i₀ j₀]
  apply completionStep_variation
  intro z
  exact listedReferenceLaw_variation r c hr hc b h hb hPL hCheeger z

/-- The implemented draw incurs one dyadic error per transition and
one more for the independent terminal completion. -/
theorem listedJointLaw_variation (x : PaperStates r c) (steps : ℕ) :
    (variation (listedJointLaw r c hr hc b h hb x steps) (stationaryJointLaw r c i₀ j₀):ℝ) ≤
      ((steps:ℝ)+1)/(2:ℝ)^h+
        ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(steps:ℝ)/(d:ℝ)^160) := by
  have hj := variation_dependentJoint_uniform
    (walkLaw (listedSmallKernel r c hr hc b h hb) x steps) (smallStationaryLaw r c i₀ j₀)
    (listedFibreLaw r c hr hc b h hb) (fun z => uniformLaw (α := PaperFibre r c z)) (1/(2:ℚ)^h)
    (listedFibreLaw_variation r c hr hc b h hb hPL hCheeger)
  have hw := walkLaw_variation (listedSmallKernel r c hr hc b h hb)
    (smallTransitionLaw r c i₀ j₀) (1/(2:ℚ)^h)
    (listedSmallKernel_variation r c hr hc b h hb hPL hCheeger) x steps
  have ht := variation_triangle
    (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
    (smallWalkLaw r c i₀ j₀ x steps) (smallStationaryLaw r c i₀ j₀)
  have he : variation (listedJointLaw r c hr hc b h hb x steps)
      (stationaryJointLaw r c i₀ j₀) ≤
      ((steps:ℚ)+1)*(1/(2:ℚ)^h)+
        variation (smallWalkLaw r c i₀ j₀ x steps) (smallStationaryLaw r c i₀ j₀) := by
    change variation (walkLaw (listedSmallKernel r c hr hc b h hb) x steps)
      (smallWalkLaw r c i₀ j₀ x steps) ≤ _ at hw
    change variation (listedJointLaw r c hr hc b h hb x steps)
      (stationaryJointLaw r c i₀ j₀) ≤ _ at hj
    linarith
  have heR := (Rat.cast_le (K := ℝ)).mpr he
  simp only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,mul_one_div] at heR
  exact heR.trans (add_le_add_right (smallWalkLaw_variation r c i₀ j₀ x steps) _)

/-- This is the manuscript's three-term bound for the actual finite
completion subroutine, ideal mixing, and first-success fallback. -/
theorem listedOuterLaw_variation [Nonempty (Table r c)]
    (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (n J₀ : ℕ) (z₀ : Table r c) :
    (variation (retryLaw (listedJointLaw r c hr hc b h hb x n)
      (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c)):ℝ) ≤
      Real.exp (-(J₀:ℝ)/(2*(1+(d:ℝ)^2)))+
      (J₀:ℝ)*(((n:ℝ)+1)/(2:ℝ)^h+
        ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160)) := by
  have hretry := retryLaw_variation (listedJointLaw r c hr hc b h hb x n)
    (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀
  have ht := variation_triangle
    (retryLaw (listedJointLaw r c hr hc b h hb x n) (stateTrial r c) z₀ J₀)
    (retryLaw (stationaryJointLaw r c i₀ j₀) (stateTrial r c) z₀ J₀) (uniformLaw (α := Table r c))
  have hrR := (Rat.cast_le (K := ℝ)).mpr hretry
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] at hrR htR
  have hj := mul_le_mul_of_nonneg_left
    (listedJointLaw_variation r c hr hc b h hb hPL hCheeger x n)
    (show (0:ℝ) ≤ J₀ by positivity)
  have hi := ideal_outer_variation r c i₀ j₀ htotal z₀ J₀
  linarith


end
end ContingencyTables.SmallGraphProfiles

end OAI
