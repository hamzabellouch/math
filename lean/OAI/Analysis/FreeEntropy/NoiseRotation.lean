import OAI.Analysis.FreeEntropy.WickBound

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeSeries
variable {α : Type}
 theorem cumulants_injective_normalized {M N : Series α} (hM : M [] = 1) (hN : N [] = 1)
    (h : cumulants M = cumulants N) : M = N := by
  have hm := moments_unique (cumulants_nil M) (cumulants_equation hM)
  have hn := moments_unique (cumulants_nil N) (cumulants_equation hN)
  rw [hm, hn, h]
end FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_cumulants (h : ℝ) (hh : 0 ≤ h) :
    cumulants (wordMoment (τ p) (X p h)) =
      cumulants (wordMoment (τ p) (C p)) + (h : ℂ) • quadratic :=
  heat_cumulants ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) h hh
 theorem doublyNoised_cumulants (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    cumulants (wordMoment (τ p) (doublyNoised p h s)) =
      cumulants (wordMoment (τ p) (C p)) + ((h+s : ℝ) : ℂ) • quadratic := by
  calc
    _ = cumulants (wordMoment (τ p) (X p h)) + (s : ℂ) • quadratic :=
      heat_cumulants (oldNoise p) (X p h) (X_mem_background p h)
        (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s hs
    _ = _ := by rw [X_cumulants p h hh]; simp [add_smul, add_assoc]
 theorem doublyNoised_law (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    wordMoment (τ p) (doublyNoised p h s) = wordMoment (τ p) (X p (h+s)) := by
  apply cumulants_injective_normalized (by simp) (by simp)
  rw [doublyNoised_cumulants p h s hh hs, X_cumulants p (h+s) (add_nonneg hh hs)]
 theorem doublyNoised_fisher_eq (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) = freeFisher (τ p) (X p (h+s)) := by
  apply freeFisher_eq_of_wordMoments (τ p) (τ p)
  · intro i
    exact heatTuple_selfAdjoint (X p h) (auxiliaryNoise p) (X_selfAdjoint p h)
      (auxiliaryNoise_selfAdjoint p) s i
  · exact X_selfAdjoint p (h+s)
  · exact congrFun (doublyNoised_law p h s hh hs)
  · exact exists_conjugate_of_fisher_le _ _ ((p+1 : ℕ)/(h+s))
      (doublyNoised_fisher_le p h s hh hs hu)
  · exact heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) (h+s) hu
end Model
end FiniteEntropySeparation

end

end OAI
