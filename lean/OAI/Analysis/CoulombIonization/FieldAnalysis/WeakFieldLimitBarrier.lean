import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BoundedL1PoissonBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma compact_pairing_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u g : Space → ℝ}
    (hg : Integrable g) (hfi : ∀ i, Integrable (fun x => f i x*g x))
    (hui : Integrable (fun x => u x*g x))
    (hc : TendstoUniformlyOn f u l (tsupport g)) :
    Tendsto (fun i => ∫ x, f i x*g x) l (𝓝 (∫ x, u x*g x)) := by
  let G := ∫ x, |g x|
  have hG : 0 ≤ G := integral_nonneg (fun _ => abs_nonneg _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(G+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc δ hδ] with i hi
  have hn := norm_integral_le_of_norm_le (hg.abs.const_mul δ)
    (f := fun x => f i x*g x-u x*g x) (ae_of_all _ (fun x => by
      rw [←sub_mul,norm_mul,Real.norm_eq_abs (g x)]
      by_cases hx : g x = 0
      · simp only [hx,abs_zero,mul_zero,le_refl]
      · have hh := (hi x (subset_tsupport g hx)).le
        rw [dist_eq_norm,norm_sub_rev] at hh
        exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)))
  rw [integral_sub (hfi i) hui,integral_const_mul] at hn
  rw [Real.dist_eq]
  have hb : δ*G < ε := by
    have he : δ*(G+1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hn' : |(∫ x, f i x*g x)-(∫ x, u x*g x)| ≤ δ*G := by
    simpa only [Real.norm_eq_abs] using hn
  exact hn'.trans_lt hb

lemma punctured_field_pairing_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u : Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) :
    Tendsto (fun i => ∫ x, f i x*Δ g x) l (𝓝 (∫ x, u x*Δ g x)) := by
  have hΔ := tfLaplacian_compact hg hcg
  exact compact_pairing_tendsto ((tfLaplacian_continuous hg).integrable_of_hasCompactSupport hΔ)
    (fun i => punctured_laplacian_pairing_integrable (hf i) hg hcg hs)
    (punctured_laplacian_pairing_integrable hu hg hcg hs)
    (hc _ hΔ (closure_minimal (fun x hx => tfLaplacian_support hg hx)
      (isClosed_tsupport g) |>.trans hs))

lemma screened_field_punctured_poisson {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    PuncturedPoisson (fun x => Z/‖x‖-tfPotential ρ x) (fun x => 4*Real.pi*ρ x) := by
  intro g hg hcg hs
  have hg0 : g 0 = 0 := by
    by_contra hn0
    exact hs (subset_tsupport g hn0) rfl
  have hni := CoulombBarrier.locallyIntegrable_mul_test
    (CoulombBarrier.nuclearField_locallyIntegrable Z)
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hpi := CoulombBarrier.locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.locallyIntegrable
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  change Integrable (fun x : Space => Z/‖x‖*Δ g x) at hni
  simp_rw [sub_mul]
  rw [integral_sub hni hpi,
    show (∫ x, Z/‖x‖*Δ g x) = -(4*Real.pi*Z)*g 0 from
      CoulombBarrier.nuclearField_weak_laplacian Z hg hcg,
    hg0,mul_zero,zero_sub,bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
  simp only [mul_assoc,integral_const_mul]
  ring

theorem punctured_poisson_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f ρ : ι → Space → ℝ} {u σ : Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hρ : ∀ i, ContinuousOn (ρ i) {0}ᶜ) (hσ : ContinuousOn σ {0}ᶜ)
    (he : ∀ i, PuncturedPoisson (f i) (ρ i))
    (hfc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    (hρc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn ρ σ l K) :
    PuncturedPoisson u σ := by
  intro g hg hcg hs
  have ht := punctured_field_pairing_tendsto hf hu hfc hg hcg hs
  have hs' := compact_pairing_tendsto (hg.continuous.integrable_of_hasCompactSupport hcg)
    (fun i => punctured_test_integrable (hρ i) hg.continuous hcg hs)
    (punctured_test_integrable hσ hg.continuous hcg hs) (hρc _ hcg hs)
  apply tendsto_nhds_unique ht
  exact hs'.congr' (Eventually.of_forall (fun i => (he i g hg hcg hs).symm))

end CoulombAnalysis

end

end OAI
