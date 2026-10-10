import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.Blowup

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings.TangentDensity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_blowup_inMeasure {f : E → F} (hf : Integrable f μ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ z ∂μ, ∀ R : ℝ, 0 < R →
      TendstoInMeasure (μ.restrict (closedBall (0:E) R))
        (fun j h => f (z+ε j • h)) atTop (fun _ => f z) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub μ hf.locallyIntegrable (1:ℝ)] with z hz
  intro R hR
  apply tendstoInMeasure_blowup μ hf hε hR
  apply hz (fun _ : ℕ => z) (fun j => ε j*R)
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun j => mul_pos (hε j) hR)⟩
    simpa using hε0.mul_const R
  · filter_upwards [] with j
    exact mem_closedBall_self (by simpa using (mul_pos (hε j) hR).le)

lemma ae_all_blowup_inMeasure {f : E → F} (hf : Integrable f μ) :
    ∀ᵐ z ∂μ, ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
      ∀ R : ℝ, 0 < R → TendstoInMeasure (μ.restrict (closedBall (0:E) R))
        (fun j h => f (z+ε j • h)) atTop (fun _ => f z) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub μ hf.locallyIntegrable (1:ℝ)] with z hz
  intro ε hε hε0 R hR
  apply tendstoInMeasure_blowup μ hf hε hR
  apply hz (fun _ : ℕ => z) (fun j => ε j*R)
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun j => mul_pos (hε j) hR)⟩
    simpa using hε0.mul_const R
  · filter_upwards [] with j
    exact mem_closedBall_self (by simpa using (mul_pos (hε j) hR).le)

lemma common_subsequence_three {α A B C : Type*} [MeasurableSpace α]
    [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
    {μ : Measure α} {f : ℕ → α → A} {g : ℕ → α → B} {h : ℕ → α → C}
    {f₀ : α → A} {g₀ : α → B} {h₀ : α → C}
    (hf : TendstoInMeasure μ f atTop f₀) (hg : TendstoInMeasure μ g atTop g₀)
    (hh : TendstoInMeasure μ h atTop h₀) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂μ,
      Tendsto (fun j => f (σ j) x) atTop (𝓝 (f₀ x)) ∧
      Tendsto (fun j => g (σ j) x) atTop (𝓝 (g₀ x)) ∧
      Tendsto (fun j => h (σ j) x) atTop (𝓝 (h₀ x)) := by
  obtain ⟨σ,hσ,hf⟩ := hf.exists_seq_tendsto_ae
  obtain ⟨τ,hτ,hg⟩ := (hg.comp hσ.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨υ,hυ,hh⟩ := (hh.comp (hσ.comp hτ).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨σ ∘ τ ∘ υ,hσ.comp (hτ.comp hυ),?_⟩
  filter_upwards [hf,hg,hh] with x hf hg hh
  exact ⟨hf.comp (hτ.comp hυ).tendsto_atTop,hg.comp hυ.tendsto_atTop,hh⟩

lemma indicator_one_eventually {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
    {q : ℕ → α} (h : Tendsto (fun j => s.indicator (fun _ => (1:ℝ)) (q j))
      atTop (𝓝 1)) : ∀ᶠ j in atTop, q j ∈ s := by
  filter_upwards [(tendsto_order.1 h).1 (1/2) (by norm_num)] with j hj
  by_contra hn
  simp only [indicator_of_notMem hn] at hj
  norm_num at hj
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma lintegral_limit_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ j, AEMeasurable (f j) μ)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    {B : ℕ → ℝ≥0∞} {L : ℝ≥0∞} (hB : ∀ j, ∫⁻ x, f j x ∂μ ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) : ∫⁻ x, g x ∂μ ≤ L := by
  calc
    ∫⁻ x, g x ∂μ = ∫⁻ x, liminf (fun j => f j x) atTop ∂μ :=
      lintegral_congr_ae (hg.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun j => ∫⁻ x, f j x ∂μ) atTop := lintegral_liminf_le' hf
    _ ≤ liminf B atTop := liminf_le_liminf (Eventually.of_forall hB)
    _ = L := hL.liminf_eq

lemma integral_limit_le {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (hf0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ f j x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    {B : ℕ → ℝ} {L : ℝ} (hB : ∀ j, ∫ x, f j x ∂μ ≤ B j)
    (hL : Tendsto B atTop (𝓝 L)) : (∫ x, g x ∂μ) ≤ L := by
  have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun j =>
    (integral_nonneg_of_ae (hf0 j)).trans (hB j))
  have hh := lintegral_limit_le (f := fun j x => ENNReal.ofReal (f j x))
    (fun j => ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hf j).aestronglyMeasurable.aemeasurable)
    (hfg.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx)
    (B := fun j => ENNReal.ofReal (B j)) (L := ENNReal.ofReal L) (fun j => ?_)
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL)
  · rw [←ofReal_integral_eq_lintegral_ofReal hg (hg0)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff hL0).mp hh
  · rw [←ofReal_integral_eq_lintegral_ofReal (hf j) (hf0 j)]
    exact ENNReal.ofReal_le_ofReal (hB j)
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X]

lemma kernel_tendsto {u ρ R : ℕ → ℝ} {u₀ ρ₀ R₀ κ β p : ℝ} (n : ℕ)
    (hu₀ : 0 < u₀) (hu : Tendsto u atTop (𝓝 u₀))
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (hR : Tendsto R atTop (𝓝 R₀)) :
    Tendsto (fun j => u j^p*ρ j/(1+κ^2*R j^2*u j^(2*β))^n) atTop
      (𝓝 (u₀^p*ρ₀/(1+κ^2*R₀^2*u₀^(2*β))^n)) := by
  exact ((hu.rpow_const (.inl hu₀.ne')).mul hρ).div
    ((tendsto_const_nhds.add ((tendsto_const_nhds.mul (hR.pow 2)).mul
      (hu.rpow_const (.inl hu₀.ne')))).pow n)
    (pow_ne_zero n (ne_of_gt (by positivity)))

noncomputable def chartExtension {s : Set E} (φ : s → X) (z : s) (x : E) : X := by
  classical
  exact if hx : x ∈ s then φ ⟨x,hx⟩ else φ z

lemma chartExtension_rescaled_tendsto {s : Set E} {φ : s → X} {z : s}
    {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0)) (h : E)
    (hs : ∀ᶠ j in atTop, (z:E)+ε j • h ∈ s) :
    Tendsto (fun j => dist (chartExtension φ z ((z:E)+ε j • h)) (φ z)/ε j)
      atTop (𝓝 (d h)) := by
  classical
  let q : ℕ → s := fun j => if hx : (z:E)+ε j • h ∈ s then ⟨(z:E)+ε j • h,hx⟩ else z
  have hq : ∀ᶠ j in atTop, (q j:E) = (z:E)+ε j • h := by
    filter_upwards [hs] with j hj
    simp [q,hj]
  have ht := MetricDifferentiation.rescaled_distance_tendsto hd hε hε0 h q hq
  apply ht.congr'
  filter_upwards [hs] with j hj
  simp [q,chartExtension,hj]

lemma chart_kernel_tendsto {s : Set E} {φ : s → X} {z : s}
    {d : Seminorm ℝ E}
    (hd : MetricDifferentiation.HasCenteredMetricDifferentialWithin s φ d z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (u ρ : E → ℝ) {κ β p : ℝ} (n : ℕ) (hu₀ : 0 < u z) (h : E)
    (hu : Tendsto (fun j => u ((z:E)+ε j • h)) atTop (𝓝 (u z)))
    (hρ : Tendsto (fun j => ρ ((z:E)+ε j • h)) atTop (𝓝 (ρ z)))
    (hχ : Tendsto (fun j => s.indicator (fun _ => (1:ℝ)) ((z:E)+ε j • h))
      atTop (𝓝 1)) :
    Tendsto (fun j => s.indicator (fun x => u x^p*ρ x /
      (1+κ^2*(dist (chartExtension φ z x) (φ z)/ε j)^2*u x^(2*β))^n)
      ((z:E)+ε j • h)) atTop
      (𝓝 (u z^p*ρ z/(1+κ^2*(d h)^2*u z^(2*β))^n)) := by
  classical
  have hs := indicator_one_eventually hχ
  have ht := kernel_tendsto (κ := κ) (β := β) (p := p) n hu₀ hu hρ
    (chartExtension_rescaled_tendsto hd hε hε0 h hs)
  apply ht.congr'
  filter_upwards [hs] with j hj
  rw [indicator_of_mem hj]
end CAT0Fillings.TangentDensity
end

end OAI
