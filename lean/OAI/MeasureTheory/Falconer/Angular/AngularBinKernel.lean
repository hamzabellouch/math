import OAI.MeasureTheory.Falconer.Fourier.SymbolProductBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

noncomputable def angularBinKernel (t : ℝ) : ℝ :=
  Real.smoothTransition (t+1) - Real.smoothTransition t

theorem angularBinKernel_contDiff : ContDiff ℝ ∞ angularBinKernel :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem angularBinKernel_nonneg (t : ℝ) : 0 ≤ angularBinKernel t :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem angularBinKernel_le_one (t : ℝ) : angularBinKernel t ≤ 1 :=
  sub_le_iff_le_add.mpr (by linarith [Real.smoothTransition.le_one (t+1),
    Real.smoothTransition.nonneg t])

theorem angularBinKernel_zero_left {t : ℝ} (ht : t ≤ -1) : angularBinKernel t = 0 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem angularBinKernel_zero_right {t : ℝ} (ht : 1 ≤ t) : angularBinKernel t = 0 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht, sub_self]

theorem angularBinKernel_tsupport : tsupport angularBinKernel ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    exact ht (angularBinKernel_zero_left (le_of_not_ge h))
  · by_contra h
    exact ht (angularBinKernel_zero_right (le_of_not_ge h))

theorem angularBinKernel_compact : HasCompactSupport angularBinKernel :=
  isCompact_Icc.of_isClosed_subset isClosed_closure angularBinKernel_tsupport

theorem angularBinKernel_two_terms {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    angularBinKernel t + angularBinKernel (t-1) = 1 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.one_of_one_le (show 1 ≤ t+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show t-1 ≤ 0 by linarith),
    sub_add_cancel]
  ring

theorem angularBinKernel_translate_zero (t : ℝ) (k : ℤ)
    (hk : k ≠ ⌊t⌋ ∧ k ≠ ⌊t⌋+1) : angularBinKernel (t-k) = 0 := by
  have hlow := Int.floor_le t
  have hhigh := Int.lt_floor_add_one t
  by_cases h : k ≤ ⌊t⌋-1
  · apply angularBinKernel_zero_right
    have hh : (k : ℝ) ≤ (⌊t⌋ : ℝ)-1 := by exact_mod_cast h
    linarith
  · apply angularBinKernel_zero_left
    have hh : ⌊t⌋+2 ≤ k := by omega
    have hh : (⌊t⌋ : ℝ)+2 ≤ (k : ℝ) := by exact_mod_cast hh
    linarith

theorem angularBinKernel_floor_partition (t : ℝ) :
    angularBinKernel (t-(⌊t⌋ : ℤ)) + angularBinKernel (t-(⌊t⌋+1 : ℤ)) = 1 := by
  have h := angularBinKernel_two_terms (sub_nonneg.mpr (Int.floor_le t))
    (show t-(⌊t⌋ : ℤ) ≤ 1 by linarith [Int.lt_floor_add_one t])
  simpa only [Int.cast_add, Int.cast_one, sub_add_eq_sub_sub] using h

end PlanarFalconer

end OAI
