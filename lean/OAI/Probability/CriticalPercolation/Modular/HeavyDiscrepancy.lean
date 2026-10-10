import Mathlib
import OAI.Probability.CriticalPercolation.Modular.NormalizedDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.DiscrepancyTail
import OAI.Probability.CriticalPercolation.Modular.HeavyThinning
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation

lemma ennreal_tendsto_zero_of_uniform_tail (f g : ℕ → ℝ≥0∞) (c b : ℕ → ℝ≥0∞)
    (hc : ∀ N, c N≠∞) (hg : Tendsto g atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hle : ∀ N n, f n≤c N*g n+b N) : Tendsto f atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh := ENNReal.half_pos hε.ne'
  obtain ⟨N,hN⟩ := (ENNReal.tendsto_nhds_zero.mp hb (ε/2) hh).exists
  have ht : Tendsto (fun n => c N*g n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr (hc N))
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht (ε/2) hh] with n hn
  exact (hle N n).trans ((add_le_add hn hN).trans_eq (ENNReal.add_halves ε))

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma clusterPeakRatio_ne_zero_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    G.clusterPeakRatio ω x≠0 := by
  obtain ⟨y,hy⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hm
  rw [G.clusterPeakRatio_eq_inv_mass hc hl ω x y hm hy]
  exact ENNReal.inv_ne_zero.mpr (fun he => hm ((G.modularMass_eq_top_change_base hc hl x y _).mpr he))

omit [Countable V] [Countable E] in
lemma normalizedDiscrepancy_le_ratio_add_tail (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (T : ℝ≥0∞)
    (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤
      (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x + G.discrepancyVolumeTail p T ω x := by
  by_cases ht : T≤G.normalizedClusterVolume ω x
  · rw [discrepancyVolumeTail,ite_eq_left ht]
    exact le_add_left le_rfl
  · by_cases hm : G.modularMass x (G.cluster ω x)=∞
    · simp only [normalizedAbsoluteDiscrepancy,hm,ENNReal.div_top,zero_le]
    · have hr := G.clusterPeakRatio_ne_zero_of_mass_ne_top hc hl ω x hm
      have hr' := ne_top_of_le_ne_top ENNReal.one_ne_top (G.clusterPeakRatio_le_one hc hl ω x)
      have hv : G.normalizedClusterVolume ω x*G.clusterPeakRatio ω x=1 := by
        rw [normalizedClusterVolume,ite_eq_right hr,ENNReal.inv_mul_cancel hr hr']
      have hone : 1≤T*G.clusterPeakRatio ω x := by
        rw [←hv]
        exact mul_le_mul_left (le_of_not_ge ht) _
      calc _ ≤ ((D*(2*K) : ℕ) : ℝ≥0∞) := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
           _ ≤ (D*(2*K) : ℕ)*T*G.clusterPeakRatio ω x := by
             simpa only [mul_one,mul_assoc] using mul_le_mul_right hone ((D*(2*K) : ℕ) : ℝ≥0∞)
           _ ≤ _ := le_add_right le_rfl

lemma expected_heavy_normalizedDiscrepancy_bound
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p q : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ u, if G.heavyFlag p u x then G.normalizedAbsoluteDiscrepancy q (atParameter q u) x else 0 ∂markLaw) ≤
      ((D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)) *
        (∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) +
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let C : ℝ≥0∞ := (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N)
  let r := fun u => if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0
  have hm : Measurable r := ((G.measurable_clusterPeakRatio x).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const
  calc
    _ ≤ ∫⁻ u, C*r u+G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x ∂markLaw := by
      apply lintegral_mono
      intro u
      by_cases h : G.heavyFlag p u x
      · simpa only [h,ite_true,r,C] using G.normalizedDiscrepancy_le_ratio_add_tail hc hl D K hD hK q
          (ENNReal.ofReal ((16:ℝ)^N)) (atParameter q u) x
      · simp only [h,ite_false,zero_le]
    _ = C*(∫⁻ u, r u ∂markLaw) + (∫⁻ ω, G.discrepancyVolumeTail q (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law q) := by
      rw [lintegral_add_left (show Measurable (fun u => C*r u) from measurable_const.mul hm),
        lintegral_const_mul'' C hm.aemeasurable]
      congr 1
      rw [show G.law q=(markLaw (E := E)).map (atParameter q) from by simpa only [BondGraph.law, BernoulliProduct.law_const] using (markLaw_map_atParameter (E := E) q).symm,
        lintegral_map (G.measurable_discrepancyVolumeTail q _ x) (measurable_atParameter q)]
    _ ≤ _ := add_le_add le_rfl (G.expected_discrepancyTail_bound hc hl hq D K hD hK q N x hx)

theorem tendsto_expected_heavy_normalizedDiscrepancy
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then
      G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0 ∂markLaw) atTop (𝓝 0) := by
  let r := fun n => ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw
  have hr : Tendsto r atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (G.tendsto_sum_expected_heavy_clusterPeakRatio hc hl hq p q hmono hqp hlim)
    · exact fun _ => zero_le
    · intro n
      exact Finset.single_le_sum (f := fun y => ∫⁻ u,
        if G.heavyFlag p u y then G.clusterPeakRatio (atParameter (q n) u) y else 0 ∂markLaw)
        (fun _ _ => zero_le) hx
  apply ennreal_tendsto_zero_of_uniform_tail _ r
    (fun N => (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N))
    (fun N => (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (ENNReal.ofReal (1/2:ℝ))^N*2)
  · intro N
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  · exact hr
  · let A : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)
    have hA : A≠∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have ht := ENNReal.Tendsto.const_mul (a := A) (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show ENNReal.ofReal (1/2:ℝ)<1 by norm_num)) (Or.inr hA)
    simpa only [mul_zero,zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr (by norm_num : (2:ℝ≥0∞)≠∞))
  · intro N n
    exact G.expected_heavy_normalizedDiscrepancy_bound hc hl hq D K hD hK p (q n) N x hx

end BondGraph
end CriticalPercolation
end
end

end OAI
