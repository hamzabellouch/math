import OAI.Probability.SLE.Mass.MassUniquenessPartitions
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Uniform finite time partitions used in the continuous-mass uniqueness proof. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

def massTimeMesh (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := T*(i:ℝ≥0)/(n+1:ℝ≥0)

@[simp] lemma massTimeMesh_zero (T : ℝ≥0) (n : ℕ) : massTimeMesh T n 0 = 0 := by
  simp [massTimeMesh]

@[simp] lemma massTimeMesh_end (T : ℝ≥0) (n : ℕ) : massTimeMesh T n (n+1) = T := by
  simp [massTimeMesh]

lemma massTimeMesh_mono (T : ℝ≥0) (n : ℕ) : Monotone (massTimeMesh T n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (show 0 ≤ T from zero_le))
    (by positivity)

lemma massTimeMesh_mem (T : ℝ≥0) (n i : ℕ) (hi : i ≤ n+1) :
    massTimeMesh T n i ∈ Icc 0 T := by
  exact ⟨zero_le,(massTimeMesh_mono T n hi).trans_eq (massTimeMesh_end T n)⟩

lemma massTimeMesh_dist (T : ℝ≥0) (n i : ℕ) :
    dist (massTimeMesh T n (i+1)) (massTimeMesh T n i) = (T:ℝ)/(n+1:ℝ) := by
  rw [NNReal.dist_eq]
  simp only [massTimeMesh,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,
    NNReal.coe_one,Nat.cast_add,Nat.cast_one]
  rw [show (T:ℝ)*(i+1:ℝ)/(n+1)-(T:ℝ)*(i:ℝ)/(n+1) = T/(n+1) by ring,
    abs_of_nonneg (by positivity)]

lemma massTimeMesh_small_increments (T : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : ContinuousOn f (Icc 0 T)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i < n+1, |f (massTimeMesh T n (i+1))-f (massTimeMesh T n i)| ≤ ε := by
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  have hlim : Tendsto (fun n : ℕ => (T:ℝ)/(n+1:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T:ℝ)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn i hi
  have h := hfδ (massTimeMesh T n (i+1)) (massTimeMesh_mem T n (i+1) (by omega))
    (massTimeMesh T n i) (massTimeMesh_mem T n i (by omega))
    (by simpa only [massTimeMesh_dist] using hn)
  exact le_of_lt (by simpa only [Real.dist_eq] using h)

lemma massDifference_mesh_variation (A B : ℝ≥0 → ℝ)
    (hA : Monotone A) (hB : Monotone B) (T : ℝ≥0) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1),
      |(A (massTimeMesh T n (i+1))-B (massTimeMesh T n (i+1)))-
        (A (massTimeMesh T n i)-B (massTimeMesh T n i))|) ≤
      (A T-A 0)+(B T-B 0) := by
  simpa only [Function.comp_def,massTimeMesh_zero,massTimeMesh_end] using
    massDifference_partition_variation (A ∘ massTimeMesh T n) (B ∘ massTimeMesh T n)
      (hA.comp (massTimeMesh_mono T n)) (hB.comp (massTimeMesh_mono T n)) (n+1)

lemma massDifference_mesh_remainder_tendsto (A B : ℝ≥0 → ℝ)
    (hA : Monotone A) (hB : Monotone B) (T : ℝ≥0)
    (hcont : ContinuousOn (fun t => A t-B t) (Icc 0 T)) :
    Tendsto (fun n => massPartitionRemainder
      (fun i => A (massTimeMesh T n i)-B (massTimeMesh T n i)) (n+1)) atTop (𝓝 0) := by
  exact massPartitionRemainder_tendsto_zero _ _ ((A T-A 0)+(B T-B 0))
    (add_nonneg (sub_nonneg.mpr (hA zero_le)) (sub_nonneg.mpr (hB zero_le)))
    (massDifference_mesh_variation A B hA hB T)
    (massTimeMesh_small_increments T _ hcont)

end SLEExactGauge

end

end OAI
