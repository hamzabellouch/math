import OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedSmooth
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalEulerBound
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse

namespace OAI

/-! The central Euler estimate for the literal typical coefficient on
the same smooth series used by the mixed convolution. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_typical_smooth_series {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction (mrtTypicalCoefficient J P F) N) s =
      ∑' n : Nat.smoothNumbers (N+1), if mrtTypical J P n then LSeries.term F s n else 0 := by
  rw [halasz_smooth_LSeries]
  apply tsum_congr
  intro n
  by_cases hn : mrtTypical J P n
  · simp [LSeries.term,mrtTypicalCoefficient,hn]
  · simp [LSeries.term,mrtTypicalCoefficient,hn]

theorem halasz_typical_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ F : ℕ → ℂ, F 1=1 →
      (∀ m n, 0 < m → 0 < n → F (m*n)=F m*F n) → OneBounded F →
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, P j ⊆ primesUpTo N) → Set.PairwiseDisjoint (J : Set ι) P →
      ‖LSeries (halaszSmoothFunction (mrtTypicalCoefficient J P F) N)
        (1+(t:ℂ)*Complex.I)‖ ≤
        C*Real.log N*Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N/2) := by
  obtain ⟨C,hC,hbound⟩ := mrt_typical_smooth_distance_bound
  refine ⟨C,hC,?_⟩
  intro F hF1 hF hFb N hN t ι J P hP hdis
  rw [halasz_typical_smooth_series]
  exact hbound F hF1 hF hFb N hN t J P hP hdis

end TwoPointCorrelations

end OAI
