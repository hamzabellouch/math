import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic

namespace OAI

/-! Join estimates from the forbidden, central, and oscillatory regions
without comparing the actions of distinct scalar channels. -/

open Set
namespace DefocusingNLS

noncomputable def spectralTruncatedAction (a : ℝ) (H : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ a then H r else 0

theorem spectralTruncatedAction_antitone (R a E : ℝ) (hRa : R ≤ a) (_haE : a ≤ E)
    (H : ℝ → ℝ) (hH : AntitoneOn H (Icc R a)) (ha : H a = 0) :
    AntitoneOn (spectralTruncatedAction a H) (Icc R E) := by
  intro r hr s hs hrs
  by_cases hsa : s ≤ a
  · have hra := hrs.trans hsa
    simp only [spectralTruncatedAction,ite_eq_left hsa,ite_eq_left hra]
    exact hH ⟨hr.1,hra⟩ ⟨hs.1,hsa⟩ hrs
  · by_cases hra : r ≤ a
    · simp only [spectralTruncatedAction,ite_eq_right hsa,ite_eq_left hra]
      exact ha ▸ hH ⟨hr.1,hra⟩ ⟨hRa,le_rfl⟩ hra
    · simp only [spectralTruncatedAction,ite_eq_right hsa,ite_eq_right hra,le_refl]

theorem spectralThreeRegion_bound (R a b E A C D B : ℝ)
    (_hRa : R ≤ a) (hab : a ≤ b) (_hbE : b ≤ E)
    (_hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 1 ≤ D) (hB : 0 ≤ B)
    (N H : ℝ → ℝ) (_ha : H a = 0)
    (hleft : ∀ r ∈ Icc R a, N r ≤ A*Real.exp (H r)*B)
    (hcentral : ∀ r ∈ Icc a b, N r ≤ C*B)
    (hright : ∀ r ∈ Icc b E, N r ≤ D*N b) :
    ∀ r ∈ Icc R E,
      N r ≤ max A (C*D)*Real.exp (spectralTruncatedAction a H r)*B := by
  intro r hr
  by_cases hra : r ≤ a
  · simp only [spectralTruncatedAction,ite_eq_left hra]
    exact (hleft r ⟨hr.1,hra⟩).trans (by gcongr; exact le_max_left _ _)
  · simp only [spectralTruncatedAction,ite_eq_right hra,Real.exp_zero,mul_one]
    by_cases hrb : r ≤ b
    · have hCD : C ≤ C*D := by nlinarith
      exact (hcentral r ⟨le_of_not_ge hra,hrb⟩).trans
        (mul_le_mul_of_nonneg_right (hCD.trans (le_max_right _ _)) hB)
    · calc
        N r ≤ D*N b := hright r ⟨le_of_not_ge hrb,hr.2⟩
        _ ≤ D*(C*B) := mul_le_mul_of_nonneg_left (hcentral b ⟨hab,le_rfl⟩) (by linarith)
        _ = (C*D)*B := by ring
        _ ≤ max A (C*D)*B := mul_le_mul_of_nonneg_right (le_max_right _ _) hB

end DefocusingNLS

end OAI
