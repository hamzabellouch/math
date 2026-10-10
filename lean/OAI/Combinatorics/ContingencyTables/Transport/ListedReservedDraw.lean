import OAI.Combinatorics.ContingencyTables.Transport.ListedDenseProgramSemantics
import OAI.Combinatorics.ContingencyTables.Dense.DenseReservedWord

namespace OAI

/-! # A common fixed word for all computed residual completion draws -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def reservedResidualDraw (z : ResidualDrawData) : DensePrograms.MatrixCode :=
  DensePrograms.reservedCanonicalDraw (residualParameters z.1,z.2)

def reservedResidualDrawRealizer : Realizer reservedResidualDraw :=
  composition (pair (composition first residualParametersRealizer) second)
    DensePrograms.reservedCanonicalDrawRealizer

theorem polynomial_reservedResidualDraw : PolynomialTime reservedResidualDrawRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_residualParameters) polynomial_second)
    DensePrograms.polynomial_reservedCanonicalDraw

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (hr : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0 < (largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "R" => listedRows r c (d^20) (d^12) (stateCapacity r c) hr
local notation "P" => listedColumns r c (d^20) (d^12) (stateCapacity r c) hc

def listedPaddedDraw (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) (bits : Fin (25*(d+b+h+1)^62) → Bool) : PaperFibre r c z :=
  listedDenseDraw r c hr hc h z (prefixWord (listedDrawBits_le r c hr hc b h hb z) bits)

theorem listedPaddedDraw_law (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool)) (listedPaddedDraw r c hr hc b h hb z)=
      mapLaw (uniformLaw (α := Fin (listedDrawBits r c hr hc h z) → Bool))
        (listedDenseDraw r c hr hc h z) :=
  padded_draw_law (listedDrawBits_le r c hr hc b h hb z) (listedDenseDraw r c hr hc h z)

theorem listedPaddedDraw_code (e : Fin q ≃ Cells (paperSmall r c))
    (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (z : PaperStates r c) (bits : Fin (25*(d+b+h+1)^62) → Bool) :
    reservedResidualDraw (((stateCodeData r c e z,d^12),(d,h)),List.ofFn bits)=
      tableOutput (paperListedEquiv r c hr hc z (listedPaddedDraw r c hr hc b h hb z bits)) := by
  have he := residualDenseDraw_code r c hr hc e h z
    (prefixWord (listedDrawBits_le r c hr hc b h hb z) bits)
  unfold residualDenseDraw at he
  rw [residualParameters_code r c hr hc e] at he
  unfold reservedResidualDraw reservedCanonicalDraw
  rw [residualParameters_code r c hr hc e]
  rw [canonicalBitCount_code (R z) (P z)
    (by have := listed_dimension_fourteen r c hr hc; omega) (listed_paper_totals r c hr hc z),
    take_ofFn_prefix (listedDrawBits_le r c hr hc b h hb z)]
  dsimp only [listedPaddedDraw]
  exact he

end
end ContingencyTables.SmallGraphProfiles

end OAI
