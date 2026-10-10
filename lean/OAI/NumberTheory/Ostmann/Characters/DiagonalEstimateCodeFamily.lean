import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesCounts
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
open InitialCharacterScale
attribute [local instance] Classical.propDecidable

def codePreservingMatchings {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Finset (Equiv.Perm (ActualCopied cfg m j)) :=
  Finset.univ.filter (fun e => ∀i, actualCopiedCode cfg m j (e i)=actualCopiedCode cfg m j i)

@[simp] theorem mem_codePreservingMatchings {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (e : Equiv.Perm (ActualCopied cfg m j)) :
    e∈codePreservingMatchings cfg m j ↔
      ∀i,actualCopiedCode cfg m j (e i)=actualCopiedCode cfg m j i := by
  simp [codePreservingMatchings]

theorem codePreservingMatchings_card_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    (codePreservingMatchings cfg m j).card ≤
      (2*m)^(2^j*m)*Fintype.card (CopiedNonbulk cfg m j)^Fintype.card (CopiedNonbulk cfg m j) := by
  have he : Fintype.card (CodePerm (actualCopiedCode cfg m j)) =
      (codePreservingMatchings cfg m j).card := Fintype.card_subtype _
  rw [←he]
  exact actualCopiedCodePerm_card_le cfg m j

def sourceNonbulkCount (k : ℕ) : ℕ := 2^k*(1+2*⌈maxCells 4 k⌉₊)

theorem sourceNonbulkCount_pos (k : ℕ) : 0<sourceNonbulkCount k := by
  unfold sourceNonbulkCount
  positivity

def sourceNonbulkLogCost (k : ℕ) : ℝ :=
  Real.log ((sourceNonbulkCount k:ℝ)^sourceNonbulkCount k)

theorem sourceNonbulkLogCost_exp (k : ℕ) :
    Real.exp (sourceNonbulkLogCost k) = (sourceNonbulkCount k:ℝ)^sourceNonbulkCount k := by
  exact Real.exp_log (pow_pos (by exact_mod_cast sourceNonbulkCount_pos k) _)

theorem copiedNonbulk_card_le_sourceNonbulkCount {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j≤k) (hcfg : (configCellCount cfg:ℝ)≤ maxCells 4 k) :
    Fintype.card (CopiedNonbulk cfg m j) ≤ sourceNonbulkCount k := by
  have hc : configCellCount cfg≤⌈maxCells 4 k⌉₊ := by
    exact_mod_cast hcfg.trans (Nat.le_ceil _)
  exact (copiedNonbulk_card_le cfg m j).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 1≤(2:ℕ)) hj)
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hc) 1))

theorem codePreservingMatchings_card_le_exp {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j≤k) (hcfg : (configCellCount cfg:ℝ)≤ maxCells 4 k) :
    ((codePreservingMatchings cfg m j).card:ℝ) ≤
      (2*(m:ℝ))^(2^j*m)*Real.exp (sourceNonbulkLogCost k) := by
  have hN := copiedNonbulk_card_le_sourceNonbulkCount cfg m j hj hcfg
  have hp : Fintype.card (CopiedNonbulk cfg m j)^Fintype.card (CopiedNonbulk cfg m j) ≤
      sourceNonbulkCount k^sourceNonbulkCount k :=
    (Nat.pow_le_pow_left hN _).trans
      (Nat.pow_le_pow_right (sourceNonbulkCount_pos k) hN)
  have hh := (codePreservingMatchings_card_le cfg m j).trans (Nat.mul_le_mul_left _ hp)
  rw [sourceNonbulkLogCost_exp]
  exact_mod_cast hh

theorem codePreserving_normalized_factor_le {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j≤k) (hcfg : (configCellCount cfg:ℝ)≤ maxCells 4 k)
    (L z C D A ε Δ W H : ℝ) (hL : 0<L) (hz : 0<z) (hm : (m:ℝ)≤z*L)
    (hH : H≤L^(-((2^j*m:ℕ):ℝ))*Real.exp (C*((2^j*m:ℕ):ℝ)+D)) :
    ((codePreservingMatchings cfg m j).card:ℝ)*H*Real.exp (-Δ+W)*
      Real.exp (A*(2:ℝ)^j*L+ε*m) ≤
    Real.exp (-Δ+((2^j*m:ℕ):ℝ)*(Real.log z+C+Real.log 2)+
      A*(2:ℝ)^j*L+ε*m+D+W+sourceNonbulkLogCost k) := by
  have hc := codePreservingMatchings_card_le_exp cfg m j hj hcfg
  calc
    _ ≤ ((codePreservingMatchings cfg m j).card:ℝ)*
        (L^(-((2^j*m:ℕ):ℝ))*Real.exp (C*((2^j*m:ℕ):ℝ)+D))*Real.exp (-Δ+W)*
        Real.exp (A*(2:ℝ)^j*L+ε*m) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ ≤ ((2*(m:ℝ))^(2^j*m)*Real.exp (sourceNonbulkLogCost k))*
        (L^(-((2^j*m:ℕ):ℝ))*Real.exp (C*((2^j*m:ℕ):ℝ)+D))*Real.exp (-Δ+W)*
        Real.exp (A*(2:ℝ)^j*L+ε*m) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (mul_nonneg (Real.rpow_nonneg hL.le _) (Real.exp_pos _).le))
        (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = (2*(m:ℝ))^(2^j*m)*(L^(-((2^j*m:ℕ):ℝ))*Real.exp (C*((2^j*m:ℕ):ℝ)+D))*
        Real.exp (-Δ+W)*Real.exp (A*(2:ℝ)^j*L+ε*m)*Real.exp (sourceNonbulkLogCost k) := by ring
    _ ≤ _ := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        code_preserving_scalar_bound (2^j) m L z C D A ε Δ W (sourceNonbulkLogCost k) hL hz hm

end Ostmann.Characters.DiagonalEstimate

end

end OAI
