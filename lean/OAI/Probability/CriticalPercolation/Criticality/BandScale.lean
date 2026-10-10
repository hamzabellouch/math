import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

def bandScale (L j : ℕ) : ℕ := L ^ (2 ^ j)

lemma bandScale_zero (L : ℕ) : bandScale L 0 = L := by simp [bandScale]
lemma bandScale_succ (L j : ℕ) : bandScale L (j + 1) = bandScale L j ^ 2 := by
  simp only [bandScale, pow_succ, pow_mul]
lemma bandScale_ge {L : ℕ} (_hL : 2 ≤ L) (j : ℕ) : L ≤ bandScale L j := by
  exact Nat.le_pow (by positivity)

lemma bandScale_tendsto {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (bandScale L) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < L)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))

lemma log_bandScale {L : ℕ} (_hL : 2 ≤ L) (j : ℕ) :
    Real.log (bandScale L j) = (2 : ℝ) ^ j * Real.log L := by
  simp [bandScale, Nat.cast_pow, Real.log_pow]

lemma band_weight {L : ℕ} (hL : 2 ≤ L) (j : ℕ) :
    (Real.log (bandScale L j))⁻¹ ^ 2 =
      (1 / 4 : ℝ) ^ j * (Real.log L)⁻¹ ^ 2 := by
  rw [log_bandScale hL, mul_inv_rev, mul_pow, mul_comm]
  congr 1
  rw [← inv_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

lemma band_weight_sum_lt {L : ℕ} (hL : 2 ≤ L) (k : ℕ) :
    ∑ j ∈ Finset.range k, (Real.log (bandScale L j))⁻¹ ^ 2 <
      4 / (3 * (Real.log L) ^ 2) := by
  have hlog : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  simp_rw [band_weight hL]
  rw [← Finset.sum_mul]
  have hg : ∑ j ∈ Finset.range k, (1/4:ℝ)^j < 4/3 := by
    have he := geom_sum_mul (1/4:ℝ) k
    have hp := pow_pos (by norm_num : (0:ℝ) < 1/4) k
    nlinarith
  have hi : 0 < (Real.log L)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hlog)
  have hm := mul_lt_mul_of_pos_right hg hi
  convert hm using 1
  simp [div_eq_mul_inv, inv_pow, mul_assoc, mul_comm, mul_left_comm]

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterBand (o : V) (s : ℕ) : Set (Set E) :=
  G.clusterTail o s \ G.clusterTail o (s ^ 2)

lemma real_clusterBand [Countable E] (p : unitInterval) (o : V) (s : ℕ) :
    (G.law p).real (G.clusterBand o s) =
      (G.law p).real (G.clusterTail o s) - (G.law p).real (G.clusterTail o (s ^ 2)) := by
  exact measureReal_sdiff (G.clusterTail_antitone o (Nat.le_pow (by omega)))
    (G.measurableSet_clusterTail o (s ^ 2))

lemma sum_real_clusterBand [Countable E] (p : unitInterval) (o : V) (L k : ℕ) :
    ∑ j ∈ Finset.range k, (G.law p).real (G.clusterBand o (bandScale L j)) =
      (G.law p).real (G.clusterTail o L) -
        (G.law p).real (G.clusterTail o (bandScale L k)) := by
  simp_rw [G.real_clusterBand, ← bandScale_succ]
  simpa only [bandScale_zero] using Finset.sum_range_sub'
    (fun j => (G.law p).real (G.clusterTail o (bandScale L j))) k

theorem exists_subcritical_clusterBand [Nonempty V]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hp : 0 < G.criticalProbability)
    (θ : ℝ) (hθ : 0 < θ)
    (hroot : ∀ o, θ ≤ (G.law G.criticalProbability).real (G.infiniteEvent o))
    (L : ℕ) (hL : 2 ≤ L) (hlarge : 4 / (3 * (Real.log L)^2) < θ / 4) :
    ∃ q : unitInterval, (G.criticalProbability : ℝ) / 2 ≤ q ∧
      q < G.criticalProbability ∧ ∃ z : V, ∃ s : ℕ, L ≤ s ∧
      (Real.log s)⁻¹ ^ 2 ≤ (G.law q).real (G.clusterBand z s) ∧
      ∀ o, θ / 2 ≤ (G.law q).real (G.clusterTail o s) := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  obtain ⟨q, hqhalf, hqpc, hq⟩ := G.subcritical_uniform_clusterTail
    hconnected hlocal hquasi G.criticalProbability hp θ hθ hroot L
  have hex : ∃ k, ∃ z : V, (G.law q).real (G.clusterTail z (bandScale L k)) < θ / 2 := by
    let o : V := Classical.arbitrary V
    have ht := (G.tendsto_real_clusterTail_subcritical hqpc o).comp (bandScale_tendsto hL)
    obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < θ/2))).exists
    exact ⟨k, o, hk⟩
  let k := Nat.find hex
  obtain ⟨z, hz⟩ := Nat.find_spec hex
  have hpre : ∀ j < k, ∀ o : V,
      θ / 2 ≤ (G.law q).real (G.clusterTail o (bandScale L j)) := by
    intro j hj o
    by_contra! h
    exact Nat.find_min hex hj ⟨o, h⟩
  have hsum : θ / 4 < ∑ j ∈ Finset.range k,
      (G.law q).real (G.clusterBand z (bandScale L j)) := by
    rw [G.sum_real_clusterBand]
    have hqz := hq z
    change (G.law q).real (G.clusterTail z (bandScale L k)) < θ / 2 at hz
    linarith
  have hexj : ∃ j ∈ Finset.range k, (Real.log (bandScale L j))⁻¹ ^ 2 ≤
      (G.law q).real (G.clusterBand z (bandScale L j)) := by
    by_contra! hj
    have hle := Finset.sum_le_sum (s := Finset.range k) (fun j hjk => (hj j hjk).le)
    have hlt := (band_weight_sum_lt hL k).trans hlarge
    linarith
  obtain ⟨j, hj, hband⟩ := hexj
  exact ⟨q, hqhalf, hqpc, z, bandScale L j, bandScale_ge hL j, hband,
    hpre j (Finset.mem_range.mp hj)⟩

end BondGraph
end CriticalPercolation
end
end

end OAI
