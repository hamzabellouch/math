import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.SphericalMeanFieldBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma rotate_ne_zero (g : SpatialRotation) {p : Space} (hp : p ≠ 0) :
    rotate g p ≠ 0 := norm_pos_iff.mp (by simpa only [(rotate g).norm_map] using norm_pos_iff.mpr hp)

lemma sphereFunction_integrable {u : Space → ℝ}
    (hu : ∀ x, x ≠ 0 → ContinuousAt u x) {p : Space} (hp : p ≠ 0) :
    Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure := by
  have hrot : Continuous (fun g : SpatialRotation => rotate g p) :=
    continuous_subtype_val.clm_apply continuous_const
  have hc : Continuous (fun g : SpatialRotation => u (rotate g p)) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (hu _ (rotate_ne_zero g hp)).comp (f := fun t : SpatialRotation => rotate t p) hrot.continuousAt
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

lemma sphereMean_close_to_constant {u : Space → ℝ} {p : Space} {A ε : ℝ}
    (hi : Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure)
    (hb : ∀ x, ‖x‖ = ‖p‖ → |u x-A| ≤ ε) :
    |sphereMean u p-A| ≤ ε := by
  have hn := norm_integral_le_of_norm_le_const (μ := rotationMeasure)
    (f := fun g : SpatialRotation => u (rotate g p)-A)
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb _ ((rotate g).norm_map p)))
  rw [integral_sub hi (integrable_const A)] at hn
  simpa only [sphereMean,integral_const,probReal_univ,smul_eq_mul,one_mul,mul_one,
    Real.norm_eq_abs] using hn

lemma sphereMean_tendsto_of_uniform {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u : Space → ℝ} {p : Space}
    (hi : ∀ i, Integrable (fun g : SpatialRotation => f i (rotate g p)) rotationMeasure)
    (hu : Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure)
    (hconv : TendstoUniformlyOn f u l (sphere (0:Space) ‖p‖)) :
    Tendsto (fun i => sphereMean (f i) p) l (𝓝 (sphereMean u p)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp hconv (ε/2) (by positivity)
  filter_upwards [he] with i hei
  have hn := norm_integral_le_of_norm_le_const (μ := rotationMeasure)
    (f := fun g : SpatialRotation => f i (rotate g p)-u (rotate g p))
    (ae_of_all _ (fun g => by
      have hh := hei (rotate g p) (by simpa only [mem_sphere,dist_zero_right] using (rotate g).norm_map p)
      simpa only [Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using hh.le))
  rw [integral_sub (hi i) hu] at hn
  have hn' : |sphereMean (f i) p-sphereMean u p| ≤ ε/2 := by
    simpa only [sphereMean,probReal_univ,mul_one,Real.norm_eq_abs] using hn
  rw [Real.dist_eq]
  linarith

attribute [local irreducible] tfPotential sphereMean

lemma mean_charge_of_bracket {ι : Type*} {l : Filter ι} [NeBot l]
    {a b t : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (ht : Tendsto t l (𝓝 0)) (hn : ∀ i, 0 ≤ a i-b i)
    (hu : ∀ i, a i-b i ≤ t i) : A = B := by
  have hzero := squeeze_zero hn hu ht
  exact sub_eq_zero.mp (tendsto_nhds_unique (ha.sub hb) hzero)

theorem sphericalMean_limit_charge {ι : Type*} {l : Filter ι} [NeBot l]
    {ρ : ι → Space → ℝ} {Z : ι → ℝ} {u : Space → ℝ} {q : ℝ} {p : Space}
    (hp : p ≠ 0) (hm : ∀ i, Measurable (ρ i)) (hi : ∀ i, Integrable (ρ i))
    (hn : ∀ i x, 0 ≤ ρ i x) (hb : ∀ i, ∃ M ≥ 0, ∀ x, ρ i x ≤ M)
    (hu : ∀ x, x ≠ 0 → ContinuousAt u x)
    (hconv : TendstoUniformlyOn (fun i x => Z i/‖x‖-tfPotential (ρ i) x)
      u l (sphere (0:Space) ‖p‖))
    (hq : Tendsto (fun i => Z i-∫ x, ρ i x) l (𝓝 q))
    (htail : Tendsto (fun i => ∫ x in {x : Space | ‖p‖ < ‖x‖}, ρ i x) l (𝓝 0)) :
    sphereMean u p = q/‖p‖ := by
  have hfi (i : ι) : Integrable
      (fun g : SpatialRotation => Z i/‖rotate g p‖-tfPotential (ρ i) (rotate g p)) rotationMeasure := by
    obtain ⟨M,hM,hMb⟩ := hb i
    have hf1 : Integrable (fun _ : SpatialRotation => Z i/‖p‖) rotationMeasure := integrable_const _
    have hf2 := potential_rotation_integrable (hm i) (hi i) hM (hn i) hMb p
    convert hf1.sub hf2 using 1
    ext g
    simp only [Pi.sub_apply,(rotate g).norm_map]
  have hs : Tendsto (fun i => sphereMean (fun x => Z i/‖x‖-tfPotential (ρ i) x) p)
      l (𝓝 (sphereMean u p)) :=
    sphereMean_tendsto_of_uniform hfi (sphereFunction_integrable hu hp) hconv
  apply mean_charge_of_bracket hs (hq.div_const ‖p‖)
    (by simpa only [zero_div] using htail.div_const ‖p‖)
  · intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact (sphereMean_field_bracket (hm i) (hi i) hM (hn i) hMb (Z i) hp).1
  · intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact (sphereMean_field_bracket (hm i) (hi i) hM (hn i) hMb (Z i) hp).2

end CoulombAnalysis

end

end OAI
