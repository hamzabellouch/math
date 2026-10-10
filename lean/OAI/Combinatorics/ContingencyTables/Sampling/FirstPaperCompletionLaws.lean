import OAI.Combinatorics.ContingencyTables.Transport.ReferenceFiniteDraw

namespace OAI

/-! # Actual finite-word completion laws for the implemented small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionCounts FairBits

lemma dyadicError_cast (n : ℕ) : ((1/(2:ℚ)^n:ℚ):ℝ)=(2:ℝ)^(-(n:ℝ)) := by
  simp only [one_div,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat,
    Real.rpow_neg_natCast,zpow_neg,zpow_natCast]


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

def finiteFibreLaw (z : PaperStates r c) : RationalLaw (PaperFibre r c z) :=
  mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool))
    (completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z))

def finiteBlockLaw (z : PaperStates r c) : RationalLaw (Table (R z) (P z)) :=
  equivLaw (paperReferenceEquiv r c i₀ j₀ z) (finiteFibreLaw r c i₀ j₀ e b h hb a fallback z)


def finiteBlockDraw (z : PaperStates r c)
    (bits : Fin (25*(d+b+h+1)^62) → Bool) : Table (R z) (P z) :=
  paperReferenceEquiv r c i₀ j₀ z (completionPaddedDraw r c i₀ j₀ e b h hb a z (fallback z) bits)

lemma finiteBlockDraw_law (z : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool))
      (finiteBlockDraw r c i₀ j₀ e b h hb a fallback z)=
      finiteBlockLaw r c i₀ j₀ e b h hb a fallback z := by
  exact mapLaw_equiv_output (paperReferenceEquiv r c i₀ j₀ z) _ _


theorem finiteFibreLaw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (z : PaperStates r c) :
    variation (finiteFibreLaw r c i₀ j₀ e b h hb a fallback z)
      (uniformLaw (α := PaperFibre r c z)) ≤ 1/(2:ℚ)^h := by
  apply (Rat.cast_le (K := ℝ)).mp
  rw [dyadicError_cast]
  unfold finiteFibreLaw
  rw [completionPaddedDraw_law]
  exact completionBooleanDraw_variation r c i₀ j₀ e hPL hCheeger h a z (fallback z)

theorem finiteBlockLaw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (z : PaperStates r c) :
    let _ : Nonempty (Table (R z) (P z)) := ⟨paperReferenceEquiv r c i₀ j₀ z (fallback z)⟩
    variation (finiteBlockLaw r c i₀ j₀ e b h hb a fallback z)
      (uniformLaw (α := Table (R z) (P z))) ≤ 1/(2:ℚ)^h := by
  let : Nonempty (Table (R z) (P z)) := ⟨paperReferenceEquiv r c i₀ j₀ z (fallback z)⟩
  dsimp only
  unfold finiteBlockLaw
  rw [←uniform_equiv (paperReferenceEquiv r c i₀ j₀ z),variation_equiv]
  exact finiteFibreLaw_variation r c i₀ j₀ e b h hb a fallback hPL hCheeger z

end
end ContingencyTables.SmallGraphProfiles

end OAI
