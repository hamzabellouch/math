import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerCoreLimit
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! The high power pressure vanishes uniformly wherever the limiting amplitude is below one. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_pressure_uniform_decay {s : Set ℝ} (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop) (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ)
    (hH : ∀ n r, r ∈ s → 0 ≤ H n r)
    (hT : TendstoUniformlyOn H A atTop s)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : ∀ r ∈ s, A r ≤ q) :
    TendstoUniformlyOn (fun n r => (H n r)^(p n-1)) (fun _ => 0) atTop s := by
  let q' := (q+1)/2
  have hq'0 : 0 ≤ q' := by dsimp [q']; linarith
  have hq'1 : q' < 1 := by dsimp [q']; linarith
  have hgap : 0 < q'-q := by dsimp [q']; linarith
  have hb : ∀ᶠ n in atTop, ∀ r ∈ s, H n r ≤ q' := by
    have ht := (Metric.tendstoUniformlyOn_iff.mp hT) (q'-q) hgap
    filter_upwards [ht] with n hn r hr
    have hd := hn r hr
    rw [Real.dist_eq] at hd
    have he := (abs_lt.mp hd).1
    have ha := hA r hr
    linarith
  have hpow : Tendsto (fun n => q'^(p n-1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq'0 hq'1).comp ((tendsto_sub_atTop_nat 1).comp hp)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεn : ∀ᶠ n in atTop, q'^(p n-1) < ε := hpow.eventually (Iio_mem_nhds hε)
  filter_upwards [hb,hεn] with n hn hεn r hr
  rw [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hH n r hr) _)]
  exact (pow_le_pow_left₀ (hH n r hr) (hn r hr) _).trans_lt hεn

/-- This is the locally uniform pressure limit required away from the limiting plateau. -/
theorem radial_pressure_decay_on_compact (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop) (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ) (s K : Set ℝ)
    (hH : ∀ n r, r ∈ s → 0 ≤ H n r) (hT : TendstoUniformlyOn H A atTop s)
    (hA : ContinuousOn A s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hK1 : ∀ r ∈ K, A r < 1) :
    TendstoUniformlyOn (fun n r => (H n r)^(p n-1)) (fun _ => 0) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · simp only [hKe, tendstoUniformlyOn_empty]
  obtain ⟨r,hr,hm⟩ := hK.exists_isMaxOn hKn (hA.mono hKs)
  apply radial_pressure_uniform_decay p hp H A (fun n r hr => hH n r (hKs hr))
    (hT.mono hKs) (max 0 (A r)) (le_max_left _ _)
  · exact max_lt (by norm_num) (hK1 r hr)
  · intro t ht
    exact (hm ht).trans (le_max_right _ _)

end DefocusingNLS

end OAI
