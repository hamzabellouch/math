import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RotationIntegralBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma annular_tf_error_local {ι : Type*} {F : Filter ι}
    {a l : ι → ℝ} {f ρ : ι → Space → ℝ} {k : ℝ}
    (ha : Tendsto a F (𝓝 0)) (hl : Tendsto l F atTop)
    (hTF : ∀ i x, a i ≤ ‖x‖ → ‖x‖ ≤ l i →
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ (l i)⁻¹^8/‖x‖^6)
    {K : Set Space} (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
    ∃ e : ι → ℝ, Tendsto e F (𝓝 0) ∧ ∀ᶠ i in F, ∀ x ∈ K,
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ e i := by
  obtain ⟨A,B,hA,_hB,hKB⟩ := compact_away_zero_annulus hK hK0
  refine ⟨fun i => (l i)⁻¹^8/A^6,?_,?_⟩
  · simpa only [Function.comp_def,zero_pow (by norm_num : (8:ℕ) ≠ 0),zero_div] using
      ((tendsto_inv_atTop_zero.comp hl).pow 8).div_const (A^6)
  · filter_upwards [ha.eventually (gt_mem_nhds hA),hl.eventually (eventually_ge_atTop B)]
      with i hi hi' x hx
    apply (hTF i x (hi.le.trans (hKB hx).1) ((hKB hx).2.trans hi')).trans
    exact div_le_div_of_nonneg_left (by positivity)
      (pow_pos hA 6) (pow_le_pow_left₀ hA.le (hKB hx).1 6)

lemma annular_upper_cap_limit {ι : Type*} {F : Filter ι} [NeBot F]
    {a l : ι → ℝ} {f : ι → Space → ℝ} {u : Space → ℝ} {C : ℝ}
    (ha : Tendsto a F (𝓝 0)) (hl : Tendsto l F atTop)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u F K)
    (hcap : ∀ᶠ i in F, ∀ x, a i ≤ ‖x‖ → ‖x‖ ≤ l i → f i x ≤ 1+C/‖x‖^4) :
    ∀ x, x ≠ 0 → u x ≤ 1+C/‖x‖^4 := by
  intro x hx
  have ht : Tendsto (fun i => f i x) F (𝓝 (u x)) :=
    (hc {x} (isCompact_singleton) (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
  apply le_of_tendsto ht
  filter_upwards [hcap,ha.eventually (gt_mem_nhds (norm_pos_iff.mpr hx)),
    hl.eventually (eventually_ge_atTop ‖x‖)] with i hi hi' hi''
  exact hi x hi'.le hi''

end CoulombAnalysis

end

end OAI
