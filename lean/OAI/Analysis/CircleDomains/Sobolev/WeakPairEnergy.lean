import OAI.Analysis.CircleDomains.Sobolev.L2WeakSubsequence
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Lower semicontinuity of the combined energy of two weakly convergent
real L² fields. Only the two pairings with the limiting fields are needed. -/
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem paired_hilbert_energy_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u₁ u₂ : ℕ → E} {v₁ v₂ : E} {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ‖u₁ n‖ ^ 2 + ‖u₂ n‖ ^ 2 ≤ B + ε n)
    (h₁ : Tendsto (fun n => inner ℝ (u₁ n) v₁) atTop (𝓝 (‖v₁‖ ^ 2)))
    (h₂ : Tendsto (fun n => inner ℝ (u₂ n) v₂) atTop (𝓝 (‖v₂‖ ^ 2))) :
    ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 ≤ B := by
  have hlim := ((h₁.add h₂).const_mul 2).sub
    (tendsto_const_nhds (x := ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2))
  have hle : ∀ᶠ n in atTop,
      2 * (inner ℝ (u₁ n) v₁ + inner ℝ (u₂ n) v₂) -
        (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) ≤ B + ε n := by
    filter_upwards [hbound] with n hn
    have hpos₁ := sq_nonneg ‖u₁ n - v₁‖
    have hpos₂ := sq_nonneg ‖u₂ n - v₂‖
    rw [norm_sub_sq_real] at hpos₁ hpos₂
    linarith
  have h := le_of_tendsto_of_tendsto hlim (tendsto_const_nhds.add hε) hle
  linarith

theorem paired_L2_energy_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u₁ u₂ : ℕ → X → ℝ} (hu₁ : ∀ n, MemLp (u₁ n) 2 μ)
    (hu₂ : ∀ n, MemLp (u₂ n) 2 μ)
    (G₁ G₂ : Lp ℝ 2 μ) {B : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (∫ x, (u₁ n x) ^ 2 + (u₂ n x) ^ 2 ∂μ) ≤ B + ε n)
    (h₁ : Tendsto (fun n => ∫ x, u₁ n x * G₁ x ∂μ) atTop
      (𝓝 (∫ x, G₁ x * G₁ x ∂μ)))
    (h₂ : Tendsto (fun n => ∫ x, u₂ n x * G₂ x ∂μ) atTop
      (𝓝 (∫ x, G₂ x * G₂ x ∂μ))) :
    (∫ x, G₁ x ^ 2 + G₂ x ^ 2 ∂μ) ≤ B := by
  have hnorm (G : Lp ℝ 2 μ) : (∫ x, G x ^ 2 ∂μ) = ‖G‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply, pow_two]
  have hpair (u : X → ℝ) (hu : MemLp u 2 μ) (G : Lp ℝ 2 μ) :
      inner ℝ (hu.toLp u) G = ∫ x, u x * G x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
  have hnormu (u : X → ℝ) (hu : MemLp u 2 μ) :
      ‖hu.toLp u‖ ^ 2 = ∫ x, u x ^ 2 ∂μ := by
    rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq hu]
  rw [integral_add (Lp.memLp G₁).integrable_sq (Lp.memLp G₂).integrable_sq,
    hnorm, hnorm]
  apply paired_hilbert_energy_le (u₁ := fun n => (hu₁ n).toLp (u₁ n))
    (u₂ := fun n => (hu₂ n).toLp (u₂ n)) hε
  · filter_upwards [hbound] with n hn
    simpa only [hnormu, integral_add (hu₁ n).integrable_sq (hu₂ n).integrable_sq] using hn
  · simpa only [hpair, ← hnorm, pow_two] using h₁
  · simpa only [hpair, ← hnorm, pow_two] using h₂

end CircleDomainRigidity

end

end OAI
