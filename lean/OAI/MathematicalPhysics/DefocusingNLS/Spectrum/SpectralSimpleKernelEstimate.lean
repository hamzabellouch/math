import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactKernelLimit

namespace OAI

/-! The estimate on a fixed complement of a simple compact-pencil kernel.
This is the quantitative input for excluding nearby additional roots. -/

open Set Filter Topology
namespace DefocusingNLS

theorem compact_approximate_kernel_limit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (v : ℕ → E)
    (hv : ∀ n, ‖v n‖ = 1) (he : Tendsto (fun n => v n - K (v n)) atTop (𝓝 0)) :
    ∃ v₀ : E, ‖v₀‖ = 1 ∧ K v₀ = v₀ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := by
  have hb (n : ℕ) : v n ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv n] using (le_refl (1 : ℝ))
  have hcomp := hK.isCompact_closure_image_closedBall 1
  obtain ⟨v₀, _, φ, hφ, ht⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem K (hb n)))
  have ht' : Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := by
    have hs := (he.comp hφ.tendsto_atTop).add ht
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using hs
  have hn : ‖v₀‖ = 1 := by
    apply tendsto_nhds_unique ht'.norm
    simpa only [hv] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hfix : K v₀ = v₀ :=
    tendsto_nhds_unique (K.continuous.continuousAt.tendsto.comp ht') ht
  exact ⟨v₀, hn, hfix, φ, hφ, ht'⟩

theorem compact_simple_kernel_estimate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (v : E)
    (L : E →L[ℂ] ℂ) (hLv : L v ≠ 0)
    (hker : ∀ u : E, K u = u → ∃ a : ℂ, u = a • v) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E, L u = 0 → c * ‖u‖ ≤ ‖u - K u‖ := by
  by_contra hfail
  push Not at hfail
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose u hu using fun n => hfail (ε n) (hε n)
  have hu0 (n : ℕ) : u n ≠ 0 := by
    intro h
    have hh := (hu n).2
    simp [h] at hh
  have hun (n : ℕ) : ‖u n‖ ≠ 0 := norm_ne_zero_iff.mpr (hu0 n)
  let w := fun n => ((‖u n‖ : ℂ)⁻¹) • u n
  have hw (n : ℕ) : ‖w n‖ = 1 := by
    dsimp [w]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (hun n)]
  have hLw (n : ℕ) : L (w n) = 0 := by
    dsimp only [w]
    rw [map_smul, (hu n).1, smul_zero]
  have hres (n : ℕ) : ‖w n - K (w n)‖ ≤ ε n := by
    have hn : 0 < ‖u n‖ := norm_pos_iff.mpr (hu0 n)
    have hid : w n - K (w n) = ((‖u n‖ : ℂ)⁻¹) • (u n - K (u n)) := by
      simp only [w, map_smul, smul_sub]
    rw [hid, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hn.le]
    calc
      ‖u n‖⁻¹ * ‖u n - K (u n)‖ ≤ ‖u n‖⁻¹ * (ε n * ‖u n‖) :=
        mul_le_mul_of_nonneg_left (hu n).2.le (inv_nonneg.mpr hn.le)
      _ = ε n := by field_simp
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => by simp only [le_add_iff_nonneg_right]; norm_num)
        tendsto_natCast_atTop_atTop
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  obtain ⟨v₀, hv₀, hfix, φ, _hφ, ht⟩ := compact_approximate_kernel_limit K hK w hw
    (squeeze_zero_norm hres hεlim)
  have hL₀ : L v₀ = 0 := by
    apply tendsto_nhds_unique (L.continuous.continuousAt.tendsto.comp ht)
    change Tendsto (fun n => L (w (φ n))) atTop (𝓝 (0 : ℂ))
    simpa only [hLw] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  obtain ⟨a, ha⟩ := hker v₀ hfix
  have ha0 : a = 0 := by
    rw [ha, map_smul, smul_eq_mul] at hL₀
    exact (mul_eq_zero.mp hL₀).resolve_right hLv
  rw [ha, ha0, zero_smul, norm_zero] at hv₀
  norm_num at hv₀

theorem kernel_complement_perturbation_estimate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K₀ K : E →L[ℂ] E) (L : E →L[ℂ] ℂ) (c : ℝ)
    (hbase : ∀ u : E, L u = 0 → c * ‖u‖ ≤ ‖u - K₀ u‖)
    (hK : ‖K - K₀‖ ≤ c / 2) (u : E) (hu : L u = 0) :
    c / 2 * ‖u‖ ≤ ‖u - K u‖ := by
  have hb := hbase u hu
  have hop := (K - K₀).le_opNorm u
  have he : u - K₀ u = (u - K u) + (K - K₀) u := by
    simp only [sub_apply]
    abel
  have ht := norm_add_le (u - K u) ((K - K₀) u)
  rw [← he] at ht
  have hm := mul_le_mul_of_nonneg_right hK (norm_nonneg u)
  linarith

theorem kernel_unique_with_normalization {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (L : E →L[ℂ] ℂ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ u : E, L u = 0 → c * ‖u‖ ≤ ‖u - K u‖)
    (u v : E) (hu : K u = u) (hv : K v = v) (hL : L u = L v) : u = v := by
  have hzero : L (u - v) = 0 := by rw [map_sub, hL, sub_self]
  have hh := hbound (u - v) hzero
  rw [map_sub, hu, hv, sub_self, norm_zero] at hh
  have hn : ‖u - v‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end DefocusingNLS

end OAI
