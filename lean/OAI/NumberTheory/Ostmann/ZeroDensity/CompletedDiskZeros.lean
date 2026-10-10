import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterCompletedZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroQuotientNormalized
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPartialSums

namespace OAI

/-! # Removing precisely the completed L-function zeros in an expanding disk -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators Classical

noncomputable def completedDiskZeros (χ : PrimitiveComplexCharacter) (R : ℝ) : Finset ℂ :=
  (criticalZerosUpTo χ (2 * R)).filter (fun z => ‖z‖ ≤ 2 * R)

@[simp] theorem mem_completedDiskZeros (χ : PrimitiveComplexCharacter) (R : ℝ) (z : ℂ) :
    z ∈ completedDiskZeros χ R ↔ ‖z‖ ≤ 2 * R ∧ χ.completed z = 0 := by
  rw [completedDiskZeros, Finset.mem_filter, mem_criticalZerosUpTo]
  constructor
  · rintro ⟨⟨hz, _⟩, hn⟩
    exact ⟨hn, (χ.completed_zero_iff z).mpr hz⟩
  · rintro ⟨hn, hz⟩
    exact ⟨⟨(χ.completed_zero_iff z).mp hz, (abs_im_le_norm z).trans hn⟩, hn⟩

theorem completed_disk_quotient_exists (χ : PrimitiveComplexCharacter) (R : ℝ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, χ.completed z = finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) (2 * R), g z ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := remove_finite_analytic_zeros χ.completed χ.completed_analytic
    χ.completed_order_ne_top (completedDiskZeros χ R)
  refine ⟨g, hg, he, ?_⟩
  intro z hz
  by_cases hm : z ∈ completedDiskZeros χ R
  · exact hne z hm
  · intro hzero
    apply hm
    refine (mem_completedDiskZeros χ R z).mpr ⟨?_, ?_⟩
    · simpa using hz
    · rw [he, hzero, mul_zero]

theorem completedDiskZeros_mass_bound (χ : PrimitiveComplexCharacter) (R : ℝ) (hR : 0 ≤ R) :
    (∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℝ)) ≤
      (32 / Real.log (14 / 13)) * (2 * R + 1) * Real.log ((χ.modulus : ℝ) * (2 * R + 2)) := by
  have he : ∀ z ∈ completedDiskZeros χ R,
      (analyticOrderNatAt χ.completed z : ℝ) = (characterZeroOrder χ z : ℝ) := by
    intro z hz
    have hr := ((χ.completed_zero_iff z).mp ((mem_completedDiskZeros χ R z).mp hz).2).1
    rw [characterZeroOrder_eq_nat]
    congr 1
    exact (congrArg ENat.toNat (χ.L_order_eq_completed z hr)).symm
  rw [Finset.sum_congr rfl he]
  apply χ.full_zero_sum_rate (2 * R) (by positivity)
  intro z hz
  obtain ⟨hn, hz0⟩ := (mem_completedDiskZeros χ R z).mp hz
  have hz' := (χ.completed_zero_iff z).mp hz0
  exact ⟨hz'.1, hz'.2.1, (abs_im_le_norm z).trans hn⟩

end Ostmann

end OAI
