import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2Dominated

namespace OAI

/-! Strong L² cutoff convergence away from a core where the input vanishes. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralL2_cutoff_tendsto (μ : Measure ℝ) (l : ℝ) (q : ℕ → ℝ → ℝ)
    (hq : ∀ n, AEStronglyMeasurable (q n) μ)
    (hb : ∀ n, ∀ᵐ r ∂μ, ‖q n r‖ ≤ 1)
    (hp : ∀ r, l < r → Tendsto (fun n => q n r) atTop (𝓝 1))
    (u : Lp ℂ 2 μ) (hu : (fun r => u r) =ᵐ[μ.restrict (Iic l)] 0) :
    Tendsto (fun n => spectralL2ComplexMultiplier μ (q n) (hq n) 1 (hb n) u)
      atTop (𝓝 u) := by
  let v := fun n => spectralL2ComplexMultiplier μ (q n) (hq n) 1 (hb n) u
  have hg : Integrable (fun r => 4*‖u r‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)).const_mul 4
  apply spectralL2_dominated_tendsto μ v u (fun r => 4*‖u r‖^2) hg
  · intro n
    filter_upwards [spectralL2ComplexMultiplier_ae μ (q n) (hq n) 1 (hb n) u,hb n]
      with r hr hbr
    have hn : ‖v n r-u r‖ ≤ 2*‖u r‖ := by
      calc
        _ ≤ ‖v n r‖+‖u r‖ := norm_sub_le _ _
        _ = ‖q n r‖*‖u r‖+‖u r‖ := by rw [show v n r=q n r • u r from hr,norm_smul]
        _ ≤ 1*‖u r‖+‖u r‖ := add_le_add (mul_le_mul_of_nonneg_right hbr (norm_nonneg (u r))) le_rfl
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith
  · have hc : ∀ᵐ r ∂μ, r ≤ l → u r=0 := by
      simpa only [mem_Iic,Pi.zero_apply] using (ae_restrict_iff' measurableSet_Iic).mp hu
    have hm : ∀ᵐ r ∂μ, ∀ n, v n r=q n r • u r :=
      ae_all_iff.mpr (fun n => spectralL2ComplexMultiplier_ae μ (q n) (hq n) 1 (hb n) u)
    filter_upwards [hc,hm] with r hc hm
    by_cases hr : r ≤ l
    · simpa only [hm,hc hr,smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · have ht := (hp r (lt_of_not_ge hr)).smul_const (u r)
      simpa only [hm,one_smul] using ht

end DefocusingNLS

end OAI
