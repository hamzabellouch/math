import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Function

theorem finite_disjoint_core_mass_bound {ι : Type*} {d : ℕ}
    (n : ℕ) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (s : Finset ι) (z : ι → Ambient d) (ρ mass : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, ENNReal.ofReal (mass i) ≤ μ (ball (z i) (ρ i)))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hsub : ∀ i ∈ s, ball (z i) (ρ i) ⊆ ball a R)
    (hdisjoint : Set.PairwiseDisjoint (s : Set ι) (fun i => ball (z i) (ρ i))) :
    ∑ i ∈ s, mass i ≤ G * R ^ n := by
  have hs : ENNReal.ofReal (∑ i ∈ s, mass i) ≤ ENNReal.ofReal (G * R ^ n) := by
    calc
      _ = ∑ i ∈ s, ENNReal.ofReal (mass i) := ENNReal.ofReal_sum_of_nonneg hmass
      _ ≤ ∑ i ∈ s, μ (ball (z i) (ρ i)) := Finset.sum_le_sum hlower
      _ = μ (⋃ i ∈ s, ball (z i) (ρ i)) :=
        (measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)).symm
      _ ≤ μ (ball a R) := measure_mono (iUnion₂_subset hsub)
      _ ≤ _ := hg.2 a R hR
  have hr := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) hs
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg hmass)] using! hr

theorem finite_AD_core_mass_packing {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (r : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hr : ∀ i ∈ s, 0 < r i)
    (hadmissible : ∀ i ∈ s, AdmissibleRadius μ (c * r i))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hcontained : ∀ i ∈ s, dist (z i) a + c * r i ≤ R)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * r i + c * r j ≤ dist (z i) (z j)) :
    ∑ i ∈ s, (r i) ^ n ≤ (C / c ^ n) * (G * R ^ n) := by
  have hd : Set.PairwiseDisjoint (s : Set ι) (fun i => ball (z i) (c * r i)) := by
    intro i hi j hj hij
    exact ball_disjoint_ball (hsep i hi j hj hij)
  have hsub : ∀ i ∈ s, ball (z i) (c * r i) ⊆ ball a R := by
    intro i hi
    apply ball_subset_ball'
    linarith [hcontained i hi]
  have hb := finite_disjoint_core_mass_bound n G μ hg s z (fun i => c * r i)
    (fun i => (c * r i) ^ n / C) (fun i hi => by have hri := hr i hi; positivity)
    (fun i hi => hlower (z i) (hz i hi) (c * r i) (hadmissible i hi)) a R hR hsub hd
  have heq : (∑ i ∈ s, (c * r i) ^ n / C) = (c ^ n / C) * ∑ i ∈ s, r i ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow]
    ring
  rw [heq] at hb
  have hcoef : 0 < c ^ n / C := div_pos (pow_pos hc n) hC
  have h : (∑ i ∈ s, r i ^ n) ≤ (G * R ^ n) / (c ^ n / C) :=
    (le_div_iff₀ hcoef).mpr (by simpa only [mul_comm] using! hb)
  convert! h using 1
  field_simp

end

end RieszRectifiability

end OAI
