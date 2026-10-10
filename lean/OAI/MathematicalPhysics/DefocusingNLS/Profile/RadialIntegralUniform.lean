import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedIntegral

namespace OAI

/-! The fixed radial integral is continuous for uniform convergence on its interval. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_integral_uniform (R : ℝ) (hR : 0 ≤ R) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hT : TendstoUniformlyOn f g atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, f n t)
      (fun r => ∫ t in (0 : ℝ)..r, g t) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(R+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδC : δ*(R+1)=ε := div_mul_cancel₀ _ (by linarith)
  have hevent := (Metric.tendstoUniformlyOn_iff.mp hT) δ hδ
  filter_upwards [hevent] with n hn r hr
  have hfn := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hr.1
    ((hf n).mono (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have hgn := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hr.1
    (hg.mono (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have hi : ‖∫ t in (0 : ℝ)..r, f n t-g t‖ ≤ δ*r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := r) (C := δ) (f := fun t => f n t-g t) (fun t ht => by
        have htI : t ∈ Icc 0 R := ⟨(uIoc_of_le hr.1 ▸ ht).1.le, (uIoc_of_le hr.1 ▸ ht).2.trans hr.2⟩
        have he := (hn t htI).le
        rwa [dist_comm,dist_eq_norm] at he)
    simpa only [sub_zero,abs_of_nonneg hr.1] using hh
  rw [dist_comm,dist_eq_norm,← intervalIntegral.integral_sub hfn hgn]
  have hprod := mul_le_mul_of_nonneg_left hr.2 hδ.le
  linarith

end DefocusingNLS

end OAI
