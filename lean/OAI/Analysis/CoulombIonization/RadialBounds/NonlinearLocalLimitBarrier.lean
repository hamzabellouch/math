import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakFieldLimitBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.WeakSommerfeldBoundsBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NonlinearLocalLimit_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom
open CoulombPDE (reaction)

lemma compact_uniformly_comp_continuous_real {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} {K : Set X} {f : ι → X → ℝ} {u : X → ℝ} {G : ℝ → ℝ}
    (hK : IsCompact K) (hu : ContinuousOn u K) (hG : Continuous G)
    (hc : TendstoUniformlyOn f u l K) :
    TendstoUniformlyOn (fun i x => G (f i x)) (fun x => G (u x)) l K := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hu
  let C := max M 0+1
  have hub (x : X) (hx : x ∈ K) : |u x| ≤ max M 0 :=
    (hM x hx).trans (le_max_left _ _)
  have huC (x : X) (hx : x ∈ K) : u x ∈ Icc (-C) C := by
    have hh := abs_le.mp (hub x hx)
    dsimp [C]
    constructor <;> linarith only [hh.1,hh.2]
  have huf := Metric.tendstoUniformlyOn_iff.mp hc 1 zero_lt_one
  have hUC : UniformContinuousOn G (Icc (-C) C) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hG.continuousOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  filter_upwards [huf,Metric.tendstoUniformlyOn_iff.mp hc δ hδ] with i h1 hi x hx
  have hfC : f i x ∈ Icc (-C) C := by
    have hh := h1 x hx
    have hub' := abs_le.mp (hub x hx)
    rw [Real.dist_eq,abs_lt] at hh
    dsimp [C]
    constructor <;> linarith only [hh.1,hh.2,hub'.1,hub'.2]
  exact hd (u x) (huC x hx) (f i x) hfC (hi x hx)

lemma uniformly_of_uniform_error {ι X : Type*} {l : Filter ι} {K : Set X}
    {f g : ι → X → ℝ} {u : X → ℝ} {e : ι → ℝ}
    (hc : TendstoUniformlyOn f u l K) (he : Tendsto e l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ x ∈ K, |g i x-f i x| ≤ e i) :
    TendstoUniformlyOn g u l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc (ε/2) (by positivity),
    he.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)),hb] with i hi hei hbi x hx
  have ht := dist_triangle (u x) (f i x) (g i x)
  have hd : dist (f i x) (g i x) ≤ e i := by
    simpa only [Real.dist_eq,abs_sub_comm] using hbi x hx
  linarith only [ht,hi x hx,hd,hei]

lemma local_tf_density_limit {ι : Type*} {l : Filter ι} {K : Set Space}
    {f ρ : ι → Space → ℝ} {u : Space → ℝ} {k : ℝ} {e : ι → ℝ}
    (hK : IsCompact K) (hu : ContinuousOn u K)
    (hc : TendstoUniformlyOn f u l K) (he : Tendsto e l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ x ∈ K,
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ e i) :
    TendstoUniformlyOn ρ (fun x => k*(max (u x-1) 0)^(3/2:ℝ)) l K := by
  exact uniformly_of_uniform_error
    (compact_uniformly_comp_continuous_real (f := f) (u := u) (G := reaction k)
      hK hu (reaction_continuous k) hc) he hb

theorem punctured_poisson_integrable_density_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f ρ : ι → Space → ℝ} {u σ : Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hρ : ∀ i, Integrable (ρ i)) (hσ : ContinuousOn σ {0}ᶜ)
    (he : ∀ i, PuncturedPoisson (f i) (ρ i))
    (hfc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    (hρc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn ρ σ l K) :
    PuncturedPoisson u σ := by
  intro g hg hcg hs
  have ht := punctured_field_pairing_tendsto hf hu hfc hg hcg hs
  obtain ⟨M,hM⟩ := hcg.exists_bound_of_continuous hg.continuous
  have hgi (i : ι) : Integrable (fun x => ρ i x*g x) := by
    apply ((hρ i).norm.const_mul M).mono'
      ((hρ i).aestronglyMeasurable.mul hg.continuous.aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      change ‖ρ i x*g x‖ ≤ M*‖ρ i x‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have ht' := compact_pairing_tendsto (hg.continuous.integrable_of_hasCompactSupport hcg)
    hgi (punctured_test_integrable hσ hg.continuous hcg hs) (hρc _ hcg hs)
  apply tendsto_nhds_unique ht
  exact ht'.congr' (Eventually.of_forall (fun i => (he i g hg hcg hs).symm))

end Work_NonlinearLocalLimit_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma tail_pairing_bound {ρ g : Space → ℝ} {R M : ℝ}
    (hi : Integrable ρ) (hn : ∀ x, 0 ≤ ρ x) ( _hM : 0 ≤ M)
    (hg : ∀ x, |g x| ≤ M) (hs : Function.support g ⊆ {x | R < ‖x‖}) :
    |∫ x, ρ x*g x| ≤ M*∫ x in {x : Space | R < ‖x‖}, ρ x := by
  let S : Set Space := {x | R < ‖x‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hh := norm_integral_le_of_norm_le ((hi.indicator hS).const_mul M)
    (f := fun x => ρ x*g x) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn x)]
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        exact (mul_le_mul_of_nonneg_left (hg x) (hn x)).trans_eq (mul_comm _ _)
      · have hgz : g x = 0 := by by_contra hh; exact hx (hs hh)
        simp only [indicator_of_notMem hx,hgz,abs_zero,mul_zero,le_refl]))
  rw [integral_const_mul,integral_indicator hS,Real.norm_eq_abs] at hh
  exact hh

theorem weak_field_tail_harmonic {ι : Type*} {l : Filter ι} [NeBot l]
    {f ρ : ι → Space → ℝ} {u : Space → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hi : ∀ i, Integrable (ρ i)) (hn : ∀ i x, 0 ≤ ρ i x)
    (he : ∀ i, PuncturedPoisson (f i) (fun x => 4*Real.pi*ρ i x))
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0))
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {x | R < ‖x‖}) : (∫ x, u x*Δ g x) = 0 := by
  have hs0 : tsupport g ⊆ {0}ᶜ := fun x hx => norm_pos_iff.mp (hR.trans (hs hx))
  obtain ⟨M,hM⟩ := hcg.exists_bound_of_continuous hg.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hb := fun i => tail_pairing_bound (hi i) (hn i) hM0
    (fun x => by simpa only [Real.norm_eq_abs] using hM x) ((subset_tsupport g).trans hs)
  have ht0 : Tendsto (fun i => ∫ x, ρ i x*g x) l (𝓝 0) :=
    squeeze_zero_norm (fun i => by simpa only [Real.norm_eq_abs] using hb i)
      (by simpa only [mul_zero] using ht.const_mul M)
  have ht' := ht0.const_mul (4*Real.pi)
  have hleft := punctured_field_pairing_tendsto hf hu hc hg hcg hs0
  apply tendsto_nhds_unique hleft
  apply (show Tendsto (fun i => 4*Real.pi*∫ x, ρ i x*g x) l (𝓝 0) by
    simpa only [mul_zero] using ht').congr'
  filter_upwards [] with i
  rw [he i g hg hcg hs0]
  simp only [mul_assoc,integral_const_mul]

end CoulombAnalysis

end

end OAI
