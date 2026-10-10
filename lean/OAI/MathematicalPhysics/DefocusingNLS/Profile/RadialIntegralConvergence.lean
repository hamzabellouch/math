import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedIntegral

namespace OAI

/-! The fixed radial integral is continuous for uniform convergence on its interval. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_integral_tendsto (R : ℝ) (hR : 0 ≤ R) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hT : TendstoUniformlyOn f g atTop (Icc 0 R)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, f n t) atTop (𝓝 (∫ t in (0 : ℝ)..R, g t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(R+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδC : δ*(R+1)=ε := div_mul_cancel₀ _ (by linarith)
  have hevent := (Metric.tendstoUniformlyOn_iff.mp hT) δ hδ
  filter_upwards [hevent] with n hn
  have hfn := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hR (hf n)
  have hgn := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hR hg
  have hi : ‖∫ t in (0 : ℝ)..R, f n t-g t‖ ≤ δ*R := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := R) (C := δ) (f := fun t => f n t-g t) (fun t ht => by
        have htI : t ∈ Icc 0 R := ⟨(uIoc_of_le hR ▸ ht).1.le,(uIoc_of_le hR ▸ ht).2⟩
        have he := (hn t htI).le
        rwa [dist_comm,dist_eq_norm] at he)
    simpa only [sub_zero,abs_of_nonneg hR] using hh
  rw [dist_eq_norm,← intervalIntegral.integral_sub hfn hgn]
  linarith

end DefocusingNLS

end OAI
