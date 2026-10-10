import OAI.Analysis.CircleDomains.Uniformization.UniformGraphCover

namespace OAI

/-! Uniform small graph covers give an actual Hausdorff-measure bound.
Only a fixed interior margin of the chosen energy neighborhood is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma uniform_graph_hausdorff_le {A O : Set GraphSpace} (μ : Measure GraphSpace)
    (K : ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : ∀ x ∈ A, closedBall x (4*δ) ⊆ O)
    (hlocal : ∀ s, 0 < s → s ≤ δ → ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    (μH[2] : Measure GraphSpace) A ≤ 4096*K*μ O := by
  let s : ℕ → ℝ := fun n => δ*(1/2:ℝ)^n
  have hs (n : ℕ) : 0 < s n := mul_pos hδ (pow_pos (by norm_num) _)
  have hsδ (n : ℕ) : s n ≤ δ := by
    dsimp only [s]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hδ.le).trans_eq (mul_one δ)
  have hst : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)))
  choose I T hcover hdiam hcost using fun n => uniform_graph_cover μ K (hs n)
    (fun x hx => (closedBall_subset_closedBall (by nlinarith [hsδ n])).trans (hsmall x hx))
    (hlocal (s n) (hs n) (hsδ n))
  let ι := fun n => Σ r : GraphGridColor, Σ i : I n r, ℕ
  have : ∀ n, Countable (ι n) := fun _ => inferInstance
  let S : (n : ℕ) → ι n → Set GraphSpace := fun n p => T n p.1 p.2.1 p.2.2
  have hD (n : ℕ) (i : ι n) : ediam (S n i) ≤ ENNReal.ofReal (8*s n) := hdiam n i.1 i.2.1 i.2.2
  have hcov (n : ℕ) : A ⊆ ⋃ i, S n i := by
    simpa only [S,ι,iUnion_sigma] using hcover n
  have hsum (n : ℕ) : (∑' i : ι n, ediam (S n i)^(2:ℝ)) ≤ 4096*K*μ O := by
    simpa only [S,ι,ENNReal.rpow_two,ENNReal.tsum_sigma'] using hcost n
  have ht : Tendsto (fun n => ENNReal.ofReal (8*s n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hst)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum 2 A _ ht S
    (Eventually.of_forall hD) (Eventually.of_forall hcov)
  apply hh.trans
  simpa only [liminf_const] using liminf_le_liminf (f := atTop) (Eventually.of_forall hsum)

end CircleDomainRigidity

end

end OAI
