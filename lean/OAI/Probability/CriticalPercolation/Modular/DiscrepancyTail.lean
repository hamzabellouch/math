import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedPeakTransport
import OAI.Probability.CriticalPercolation.Modular.GeometricPeakBand
import OAI.Probability.CriticalPercolation.Modular.NormalizedDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace CriticalPercolation

lemma ennreal_geometric_band (v : ℝ≥0∞) (hv : v≠∞) (N : ℕ)
    (hN : ENNReal.ofReal ((16:ℝ)^N)≤v) :
    ∃ m : ℕ, ENNReal.ofReal ((16:ℝ)^(N+m))≤v ∧ v<ENNReal.ofReal ((16:ℝ)^(N+m+1)) := by
  have hNr : (16:ℝ)^N≤v.toReal := (ENNReal.ofReal_le_iff_le_toReal hv).mp hN
  have hone : 1≤v.toReal := (one_le_pow₀ (by norm_num : (1:ℝ)≤16)).trans hNr
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hone (by norm_num : (1:ℝ)<16)
  have hNk : N≤k := by
    by_contra h
    have hkle : k+1≤N := by omega
    have hp : (16:ℝ)^(k+1)≤16^N := pow_le_pow_right₀ (by norm_num) hkle
    exact (not_lt_of_ge hNr) (hk'.trans_le hp)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hNk
  exact ⟨m,ENNReal.ofReal_le_of_le_toReal hk,(ENNReal.lt_ofReal_iff_toReal_lt hv).mpr hk'⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma normalizedClusterVolume_ne_top (ω : Set E) (x : V) : G.normalizedClusterVolume ω x≠∞ := by
  unfold normalizedClusterVolume
  split_ifs with h
  · exact ENNReal.zero_ne_top
  · exact ENNReal.inv_ne_top.mpr h

def discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (ω : Set E) (x : V) : ℝ≥0∞ :=
  if T≤G.normalizedClusterVolume ω x then G.normalizedAbsoluteDiscrepancy p ω x else 0

lemma measurable_discrepancyVolumeTail (p : ℝ) (T : ℝ≥0∞) (x : V) :
    Measurable (fun ω : Set E => G.discrepancyVolumeTail p T ω x) :=
  (G.measurable_normalizedAbsoluteDiscrepancy p x).ite
    (measurableSet_le measurable_const (G.measurable_normalizedClusterVolume x)) measurable_const

omit [Countable V] [Countable E] in
lemma discrepancyVolumeTail_le_bands (p : ℝ) (N : ℕ) (ω : Set E) (x : V) :
    G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ≤
      ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := by
  unfold discrepancyVolumeTail
  split_ifs with h
  · obtain ⟨m,hm⟩ := ennreal_geometric_band _ (G.normalizedClusterVolume_ne_top ω x) N h
    calc
      _ = G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x := (ite_eq_left hm).symm
      _ ≤ _ := ENNReal.le_tsum (f := fun index : ℕ =>
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+index)))
          (ENNReal.ofReal ((16:ℝ)^(N+index+1))) ω x) m
  · exact zero_le

lemma expected_discrepancyTail_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (N : ℕ)
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    (∫⁻ ω, G.discrepancyVolumeTail p (ENNReal.ofReal ((16:ℝ)^N)) ω x ∂G.law p) ≤
      (G.orbitRepresentatives hq).roots.card *
        ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
          (ENNReal.ofReal (1/2:ℝ))^N*2 := by
  let A : ℝ := 5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1
  let R : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card
  calc
    _ ≤ ∫⁻ ω, ∑' m : ℕ, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_mono (fun ω => G.discrepancyVolumeTail_le_bands p N ω x)
    _ = ∑' m : ℕ, ∫⁻ ω, G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
        (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω x ∂G.law p :=
      lintegral_tsum (fun m => (G.measurable_discrepancyVolumeBand p _ _ x).aemeasurable)
    _ ≤ ∑' m : ℕ, R * ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      exact (Finset.single_le_sum (f := fun y => ∫⁻ ω,
        G.discrepancyVolumeBand p (ENNReal.ofReal ((16:ℝ)^(N+m)))
          (ENNReal.ofReal ((16:ℝ)^(N+m+1))) ω y ∂G.law p) (fun _ _ => zero_le) hx).trans
        (G.expected_discrepancyBand_geometric hc hl hq D K hD hK p (N+m))
    _ = _ := by
      have he (m : ℕ) : ENNReal.ofReal (A*(1/2:ℝ)^(N+m)) =
          ENNReal.ofReal A * (ENNReal.ofReal (1/2:ℝ))^N * (ENNReal.ofReal (1/2:ℝ))^m := by
        rw [ENNReal.ofReal_mul (show 0≤A by dsimp [A]; positivity),
          ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),pow_add,mul_assoc]
      simp_rw [he,←mul_assoc]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      norm_num [R,A,ENNReal.ofReal_div_of_pos]

end BondGraph
end CriticalPercolation
end
end

end OAI
