import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.OriginalDyadicTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem finite_sum_of_bounded_level_slices {ι : Type*}
    (s : Finset ι) (level : ι → ℕ) (mass : ι → ℝ) (N : ℕ) (B : ℝ)
    (hlevel : ∀ i ∈ s, level i < N)
    (hslice : ∀ k < N, ∑ i ∈ s with level i = k, mass i ≤ B) :
    ∑ i ∈ s, mass i ≤ (N : ℝ) * B := by
  classical
  have hsum : (∑ k ∈ Finset.range N, ∑ i ∈ s with level i = k, mass i) = ∑ i ∈ s, mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_range.mpr (hlevel i hi)) mass
  rw [← hsum]
  calc
    _ ≤ ∑ _k ∈ Finset.range N, B := Finset.sum_le_sum (fun k hk => hslice k (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem DyadicOscillationTests.coarse_level_packing {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ} (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (s : Finset ι) (N : ℕ) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hradii : ∀ i ∈ s, F.radius i ≤ R) :
    ∑ i ∈ s with F.level i < N, F.radius i ^ n ≤
      ((N : ℝ) * ((C / c ^ n) * G * (1 + c) ^ n)) * R ^ n := by
  classical
  let t := s.filter (fun i => F.level i < N)
  have hb := finite_sum_of_bounded_level_slices t F.level (fun i => F.radius i ^ n) N
    (((C / c ^ n) * G * (1 + c) ^ n) * R ^ n)
    (fun i hi => (Finset.mem_filter.mp hi).2) (by
      intro k _
      let q := t.filter (fun i => F.level i = k)
      have hqs (i : ι) (hi : i ∈ q) : i ∈ s :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have hbound := finite_AD_core_mass_packing n C G hC μ hg hlower q F.center F.radius c hc
        (fun i _ => F.center_mem i) (fun i _ => F.radius_pos i) (fun i _ => F.core_admissible i)
        a ((1 + c) * R) (by positivity)
        (by
          intro i hi
          have hcR := mul_le_mul_of_nonneg_left (hradii i (hqs i hi)) hc.le
          linarith [hcenters i (hqs i hi)])
        (by
          intro i hi j hj hij
          exact F.separated i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij)
      simpa only [mul_pow, mul_assoc] using! hbound)
  simpa only [mul_assoc] using! hb

end

end RieszRectifiability

end OAI
