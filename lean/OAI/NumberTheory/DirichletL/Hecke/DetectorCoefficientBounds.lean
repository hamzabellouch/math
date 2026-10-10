import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual
import OAI.NumberTheory.DirichletL.Hecke.DetectorTail

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorCoefficientBounds
open HeckeFamily HeckeDetectorFourier HeckeDetectorTail
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma annular_norm_le_two (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖DyadicTransfer.annularCutoff V x‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [hV x,hV (2*x)])

lemma inverseCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

def expandedSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U^21⌉₊

lemma expandedSet_count (U : ℝ) (hU : 1 ≤ U) :
    ((expandedSet U).card : ℝ) ≤ 4096*U^21 := by
  have hp : 1 ≤ U^21 := one_le_pow₀ hU
  have hc : (1 : ℝ) ≤ ⌈16*U^21⌉₊ := (by linarith : (1 : ℝ) ≤ 16*U^21).trans (Nat.le_ceil _)
  have h := DescentFiberCost.finite_ideal_count_real (expandedSet U) (⌈16*U^21⌉₊ : ℝ) hc
    (fun I hI => Ideal.absNorm_eq_zero_iff.not.mp (by have := (mem_idealsUpTo.mp hI).1; omega))
    (fun I hI => by exact_mod_cast (mem_idealsUpTo.mp hI).2)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16*U^21 by positivity)
  linarith

theorem coefficient_mass (χ : Character) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end SevenEighths.HeckeDetectorCoefficientBounds

end

end OAI
