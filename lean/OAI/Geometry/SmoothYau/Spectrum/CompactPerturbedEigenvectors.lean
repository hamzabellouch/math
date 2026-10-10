import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ContinuousEigenpairLinearization

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
omit [CompleteSpace X] in
lemma compact_perturbed_eigenvectors (T : X →L[ℝ] X) (hT : IsCompactOperator T)
    (S : ℕ → X →L[ℝ] X) (hS : Tendsto S atTop (𝓝 T)) {μ : ℝ} (hμ : μ ≠ 0)
    (z : ℕ → X) (hz : ∀ n, ‖z n‖ = 1) (he : ∀ n, S n (z n) = μ • z n) :
    ∃ v : X, ‖v‖ = 1 ∧ T v = μ • v ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (z ∘ φ) atTop (𝓝 v) := by
  obtain ⟨K,hK,hKi⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y,_,φ,hφ,hy⟩ := hK.tendsto_subseq (fun n =>
    hKi ⟨z n, by simp only [Metric.mem_closedBall, dist_zero_right, hz n, le_refl], rfl⟩)
  have hd : Tendsto (fun n => (S n - T) (z n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb (n : ℕ) : ‖(S n - T) (z n)‖ ≤ ‖S n - T‖ := by
      simpa only [hz, mul_one] using (S n - T).le_opNorm (z n)
    have hl : Tendsto (fun n => ‖S n - T‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hS.sub (tendsto_const_nhds (x := T))).norm
    exact squeeze_zero (fun n => norm_nonneg _) hb hl
  have hzlim : Tendsto (z ∘ φ) atTop (𝓝 (μ⁻¹ • y)) := by
    have hh := (hy.add (hd.comp hφ.tendsto_atTop)).const_smul μ⁻¹
    simp only [add_zero] at hh
    convert hh using 1
    funext n
    change z (φ n) = μ⁻¹ • (T (z (φ n)) + (S (φ n) (z (φ n)) - T (z (φ n))))
    rw [he]
    have hx : T (z (φ n)) + (μ • z (φ n) - T (z (φ n))) = μ • z (φ n) := by abel
    rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hn : ‖μ⁻¹ • y‖ = 1 := by
    apply tendsto_nhds_unique hzlim.norm
    simpa only [Function.comp_apply, hz] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hte : T (μ⁻¹ • y) = μ • (μ⁻¹ • y) := by
    have hc : Continuous (fun p : (X →L[ℝ] X) × X => p.1 p.2) := by fun_prop
    have hh := hc.tendsto (T, μ⁻¹ • y) |>.comp
      ((hS.comp hφ.tendsto_atTop).prodMk_nhds hzlim)
    have hh' := hzlim.const_smul μ
    apply tendsto_nhds_unique hh
    simpa only [Function.comp_def, he] using hh'
  exact ⟨_,hn,hte,φ,hφ,hzlim⟩

namespace PositivePairing
variable (B : PositivePairing (X := X))

omit [CompleteSpace X] in
theorem pinned_weak_first_variation (T : ℝ → X →L[ℝ] X)
    (test : X → ℝ → X →L[ℝ] ℝ) (test₀ : X → X →L[ℝ] ℝ)
    (hcompact : IsCompactOperator (T 0))
    (hT : Tendsto T (𝓝 (0 : ℝ)) (𝓝 (T 0)))
    {μ : ℝ} (hμ : μ ≠ 0) {u : X} (hu0 : u ≠ 0)
    (hu : ∀ᶠ t in 𝓝[≠] (0 : ℝ), T t u = μ • u)
    (hlim : ∀ a, T 0 a = μ • a →
      Tendsto (test a) (𝓝[≠] (0 : ℝ)) (𝓝 (test₀ a)))
    (hvan : ∀ a, T 0 a = μ • a → ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∀ z, T t z = μ • z → test a t z = 0)
    (hnd : ∀ z, T 0 z = μ • z → B.form u z = 0 →
      (∀ v, T 0 v = μ • v → B.form u v = 0 → test₀ v z = 0) → z = 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ z, T t z = μ • z → ∃ c : ℝ, z = c • u := by
  have hker : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ z,
      T t z = μ • z → B.form u z = 0 → z = 0 := by
    by_contra hbad
    have hf : ∃ᶠ t in 𝓝[≠] (0 : ℝ), ∃ z,
        T t z = μ • z ∧ B.form u z = 0 ∧ z ≠ 0 := by
      simpa only [not_eventually, not_forall, Classical.not_imp, exists_prop] using hbad
    obtain ⟨t,htlim,ht⟩ := exists_seq_forall_of_frequently hf
    choose z hze hzp hzn using ht
    let w : ℕ → X := fun n => ‖z n‖⁻¹ • z n
    have hwn : ∀ n, ‖w n‖ = 1 := by
      intro n
      simp only [w, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hzn n))]
    have hwe : ∀ n, T (t n) (w n) = μ • w n := by
      intro n
      simp only [w, map_smul, hze]
      exact smul_comm _ _ _
    have hwp : ∀ n, B.form u (w n) = 0 := by
      intro n
      simp only [w, map_smul, hzp, smul_zero]
    have ht0 : Tendsto t atTop (𝓝 (0 : ℝ)) := htlim.mono_right nhdsWithin_le_nhds
    obtain ⟨v,hvn,hve,φ,hφ,hv⟩ := compact_perturbed_eigenvectors (T 0) hcompact
      (T ∘ t) (hT.comp ht0) hμ w hwn hwe
    have hvp : B.form u v = 0 := by
      apply tendsto_nhds_unique ((B.form u).continuous.tendsto v |>.comp hv)
      simpa only [Function.comp_def, hwp] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hzero : v = 0 := hnd v hve hvp (by
      intro a hae _hap
      have hc : Continuous (fun p : (X →L[ℝ] ℝ) × X => p.1 p.2) := by fun_prop
      have hdv := hc.tendsto (test₀ a,v) |>.comp
        (((hlim a hae).comp htlim |>.comp hφ.tendsto_atTop).prodMk_nhds hv)
      apply tendsto_nhds_unique hdv
      apply tendsto_const_nhds.congr'
      filter_upwards [hφ.tendsto_atTop.eventually (htlim.eventually (hvan a hae))] with j hj
      exact (hj _ (hwe (φ j))).symm)
    rw [hzero, norm_zero] at hvn
    exact zero_ne_one hvn
  filter_upwards [hker,hu] with t ht htu z hz
  let c : ℝ := B.form u z / B.form u u
  have he : T t (z - c • u) = μ • (z - c • u) := by
    simp only [map_sub, map_smul, htu, hz, smul_sub]
    rw [smul_comm c μ u]
  have hp : B.form u (z - c • u) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, c]
    rw [div_mul_cancel₀ _ (B.positive u hu0).ne', sub_self]
  exact ⟨c, sub_eq_zero.mp (ht _ he hp)⟩
end PositivePairing
end YauCounterexamples
end

end OAI
