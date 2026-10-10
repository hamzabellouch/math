import OAI.NumberTheory.JointDickman.Amplification.ArithmeticProfilePreservation
import OAI.NumberTheory.JointDickman.Probability.ResidueProfileLimits

namespace OAI

/-! # Nonzero arithmetic correlations survive smooth amplification -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_norm_lower {β : ℂ} (hβ : β ≠ 0) {d : ℝ} (hd : 0 < d)
    (u : ℕ → ℂ) (m : ℕ → ℝ)
    (hm : ∀ᶠ B : ℕ in atTop, d ≤ m B)
    (he : Tendsto (fun B => u B - β * (m B : ℂ)) atTop (nhds 0)) :
    ∀ᶠ B : ℕ in atTop, d/2 * ‖β‖ ≤ ‖u B‖ := by
  have hpos : 0 < d/2 * ‖β‖ := mul_pos (half_pos hd) (norm_pos_iff.mpr hβ)
  have he' := (Metric.tendsto_nhds.mp he) (d/2 * ‖β‖) hpos
  filter_upwards [hm,he'] with B hB heB
  rw [dist_zero_right] at heB
  have hm0 : 0 ≤ m B := le_trans hd.le hB
  have ht := norm_sub_le (u B) (u B - β * (m B : ℂ))
  have hid : u B - (u B - β * (m B : ℂ)) = β * (m B : ℂ) := by ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0] at ht
  nlinarith [mul_le_mul_of_nonneg_right hB (norm_nonneg β)]

/-- The positive lower constant is independent of the later fixed regularity
cutoff. The outer limit is still conditional only on the cited analytic inputs. -/
theorem smooth_amplified_profile_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (W : ResidueProfile) (hW : W.mean ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ T : ℕ → ℕ,
        (∀ᶠ B : ℕ in atTop, 0 < T B ∧ (T B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B)) →
        ∀ᶠ B : ℕ in atTop, d * ‖W.mean‖ ≤
          ‖W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C (T B))‖ := by
  obtain ⟨d,hd,hl⟩ := smooth_arithmetic_first_lower hFord hSD hM hMP
  refine ⟨d/2,half_pos hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC T hT
  apply amplification_norm_lower hW hd
    (fun B => W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C (T B)))
    (fun B => arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B (T B)) 1)
  · filter_upwards [hb,hT] with B hB hTB
    exact hB C (T B) hC hTB.1 hTB.2
  · exact smooth_arithmetic_profile_preservation hFord hM W L τ C T hT

/-- A single extracted subsequence supplies all the inner arithmetic limits.
The profile and its bounds are constructed from the bounded array. -/
theorem exists_arithmetic_amplification_profile (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) {β : ℂ}
    (hmean : Tendsto (fun N => (∑ n ∈ range N, H N n) / (N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ W : ResidueProfile, W.mean = β ∧
      ∀ (B L : ℕ) (τ C' : ℝ) (T : ℕ),
        Tendsto (fun N => (∑ n ∈ range (s N), H (s N) n *
          (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ)) / (s N : ℂ))
          atTop (nhds (W.correlation (amplificationPeriod B)
            (smoothResidueAmplification B L τ C' T))) := by
  obtain ⟨s,hs,W,_,hW⟩ := exists_residueProfile H hC hH
  have hm := hW 1 (fun _ => 1)
  simp only [empiricalResidueTest, mul_one] at hm
  have hβ : W.mean = β := tendsto_nhds_unique hm (hmean.comp hs.tendsto_atTop)
  refine ⟨s,hs,W,hβ,?_⟩
  intro B L τ C' T
  have h := hW (amplificationPeriod B) (smoothResidueAmplification B L τ C' T)
  have he (n : ℕ) : smoothResidueAmplification B L τ C' T (n : ZMod (amplificationPeriod B : ℕ)) =
      (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ) := by
    exact congrArg (fun r : ℝ => (r : ℂ))
      (residueAmplification_natCast B L n τ C' (amplificationSmoothWeight B T))
  simpa only [empiricalResidueTest, he, ResidueProfile.correlation] using h

end JointDickman

end OAI
