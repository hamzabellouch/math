import OAI.Analysis.CircleDomains.Sobolev.MaximalTruncations

namespace OAI

/-! Pass the bounded maximal estimate through increasing compact truncations.
The finite L² limit dominates every original ball integral almost everywhere. -/
open Set Function Filter MeasureTheory Metric DiskMaximalTools
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem nonnegative_maximal_L2 {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) :
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ MemLp m 2 volume ∧
      (∫ x, m x^2) ≤ 200*(∫ x, f x^2) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
        (∫ y in ball x r, f y) ≤ volume.real (ball x r)*m x := by
  have hb (n : ℕ) := bounded_maximal_L2 (measurable_maximalInputTruncation hf n)
    (maximalInputTruncation_nonneg hf0 n) (maximalInputTruncation_integrable hf hf0 hf2 n)
    (maximalInputTruncation_memLp hf hf0 hf2 n) (maximalInputTruncation_le_bound (f := f) n)
  choose m hm hm0 hm2 hE hav hme using hb
  have hmono (x : ℂ) : Monotone (fun n => m n x) := by
    intro i j hij
    have hν : volume.withDensity (fun y => ENNReal.ofReal (maximalInputTruncation f i y)) ≤
        volume.withDensity (fun y => ENNReal.ofReal (maximalInputTruncation f j y)) :=
      withDensity_mono (ae_of_all _ (fun y =>
        ENNReal.ofReal_le_ofReal (maximalInputTruncation_mono hf0 y hij)))
    have hle : ENNReal.ofReal (m i x) ≤ ENNReal.ofReal (m j x) := by
      rw [hme i x, hme j x]
      unfold rationalMaximal
      apply iSup_mono
      intro q
      apply iSup_mono
      intro _
      exact ENNReal.div_le_div_right (hν (ball x (q : ℝ))) _
    exact (ENNReal.ofReal_le_ofReal_iff (hm0 j x)).mp hle
  have hB : 0 ≤ 200*(∫ x, f x^2) := mul_nonneg (by norm_num)
    (integral_nonneg (fun x => sq_nonneg (f x)))
  obtain ⟨P, hP, hP0, hP2, hPE, hlim⟩ := exists_monotone_L2_limit hm hm2 hm0 hmono hB
    (fun n => (hE n).trans (mul_le_mul_of_nonneg_left
      (maximalInputTruncation_energy_le hf hf0 hf2 n) (by norm_num)))
  refine ⟨P, hP, hP0, hP2, hPE, ?_⟩
  intro r hr
  filter_upwards [hlim] with x hx
  apply le_of_tendsto (tendsto_integral_maximalInputTruncation hf hf0 hf2 x r)
  exact Eventually.of_forall (fun n => (hav n x r hr).trans
    (mul_le_mul_of_nonneg_left (hx.2 n) measureReal_nonneg))

end CircleDomainRigidity

end

end OAI
