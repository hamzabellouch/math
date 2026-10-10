import OAI.Analysis.CircleDomains.Uniformization.HeightVanishingConvergence

namespace OAI

/-! A common error threshold for all heights in an equicontinuous,
normalized family. The threshold may depend on the compact test set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem uniform_height_closeness {ι : Type*}
    (v : ι → C(ℂ, ℝ)) (G₀ G₁ : ι → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ i, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ i) (G₁ i))
      (v i ∘ complexPlaneCoordinates) univ)
    (heq : Equicontinuous (fun i z => v i z))
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ i z, z ∈ K → |v i z| ≤ C)
    (e : ι → ℝ) (hE : ∀ i, (∫ p, G₀ i p^2+G₁ i p^2) ≤ e i)
    {R A : ℝ} (hd : ∀ i z, R ≤ ‖z‖ → |v i z-z.im| ≤ A/‖z‖)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i, e i < δ → ∀ z ∈ K, |v i z-z.im| < ε := by
  by_contra hn
  push Not at hn
  have hbad (n : ℕ) : ∃ i, e i < 1/((n : ℝ)+1) ∧
      ∃ z ∈ K, ε ≤ |v i z-z.im| := hn _ (by positivity)
  choose ix hix z hz hbadz using hbad
  have hn0 (i : ι) : 0 ≤ e i :=
    (integral_nonneg (fun p => add_nonneg (sq_nonneg (G₀ i p)) (sq_nonneg (G₁ i p)))).trans (hE i)
  have he : Tendsto (fun n => e (ix n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      (fun n => hn0 (ix n)) (fun n => (hix n).le)
  have hlim := heights_tendsto_vertical_of_energy (v ∘ ix) (G₀ ∘ ix) (G₁ ∘ ix)
    (fun n => hw (ix n)) (heq.comp ix)
    (fun L hL => by
      obtain ⟨C, hC⟩ := hb L hL
      exact ⟨C, fun n => hC (ix n)⟩)
    he (fun n => hE (ix n)) (fun n => hd (ix n))
  have hU := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.tendstoLocallyUniformlyOn.mono (subset_univ K))
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hU ε hε).exists
  have hclose : |v (ix n) (z n)-(z n).im| < ε := by
    simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hn (z n) (hz n)
  exact (not_lt_of_ge (hbadz n)) hclose

end CircleDomainRigidity

end

end OAI
