import OAI.Analysis.CircleDomains.Topology.FiniteBallSynthesis
import OAI.Analysis.CircleDomains.Sobolev.MonotoneL2Limit

namespace OAI

/-! Monotone convergence completes ball synthesis for the countable
balloon family. The density is the actual sum of weighted indicators. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def countableBallDensity (c : ℕ → ℂ) (d a : ℕ → ℝ) (z : ℂ) : ℝ :=
  ∑' j, (ball (c j) (d j)).indicator (fun _ => a j/d j) z

 theorem exists_countable_ball_synthesis_constant (hmax : PlanarMaximalL2) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (d a : ℕ → ℝ) (E : ℕ → Set ℂ),
      (∀ j, 0 < d j) → (∀ j, 0 ≤ a j) → Summable (fun j => a j^2) →
      (∀ j, MeasurableSet (E j)) → Pairwise (Disjoint on E) →
      (∀ j, E j ⊆ ball (c j) (d j)) → (∀ j, a j ≠ 0 → k*d j^2 ≤ volume.real (E j)) →
      MemLp (countableBallDensity c d a) 2 volume ∧
      (∫ z, countableBallDensity c d a z^2) ≤ C*(∑' j, a j^2) ∧
      (∀ᵐ z ∂volume, ∀ n, finiteBallDensity (Finset.range n) c d a z ≤ countableBallDensity c d a z) := by
  obtain ⟨C,hC,hfinite⟩ := exists_finite_ball_synthesis_constant hmax hk
  refine ⟨C,hC,?_⟩
  intro c d a E hd ha ha2 hE hdisj hsub hsize
  let f := fun n => finiteBallDensity (Finset.range n) c d a
  have hf (n : ℕ) : Measurable (f n) := by
    exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator measurableSet_ball)
  have hf0 (n : ℕ) (z : ℂ) : 0 ≤ f n z :=
    finiteBallDensity_nonneg _ c (fun j _ => ha j) (fun j _ => (hd j).le) z
  have hterm (z : ℂ) (j : ℕ) : 0 ≤ (ball (c j) (d j)).indicator (fun _ => a j/d j) z :=
    indicator_nonneg (fun _ _ => div_nonneg (ha j) (hd j).le) z
  have hmono (z : ℂ) : Monotone (fun n => f n z) := by
    intro n m hnm
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) (fun j _ _ => hterm z j)
  have hB : 0 ≤ C*(∑' j, a j^2) := mul_nonneg hC.le (tsum_nonneg (fun j => sq_nonneg (a j)))
  have hbound (n : ℕ) : (∫ z, f n z^2) ≤ C*(∑' j, a j^2) := by
    classical
    let F := (Finset.range n).filter (fun j => a j ≠ 0)
    have he : f n = finiteBallDensity F c d a :=
      (finiteBallDensity_filter_ne_zero (Finset.range n) c d a).symm
    rw [he]
    exact (hfinite F c d a E (fun j _ => hd j) (fun j _ => ha j)
      (fun j _ => hE j) (fun i _ j _ hij => hdisj hij) (fun j _ => hsub j)
      (fun j hj => hsize j (Finset.mem_filter.mp hj).2)).trans
      (mul_le_mul_of_nonneg_left (ha2.sum_le_tsum _ (fun j _ => sq_nonneg (a j))) hC.le)
  obtain ⟨P,_,_,hP,henergy,hlim⟩ := exists_monotone_L2_limit hf
    (fun n => finiteBallDensity_memLp (Finset.range n) c d a) hf0 hmono hB hbound
  have heq : countableBallDensity c d a =ᵐ[volume] P := by
    filter_upwards [hlim] with z hz
    have hs : HasSum (fun j => (ball (c j) (d j)).indicator (fun _ => a j/d j) z) (P z) :=
      (hasSum_iff_tendsto_nat_of_nonneg (hterm z) (P z)).mpr hz.1
    exact hs.tsum_eq
  refine ⟨hP.ae_eq heq.symm,?_,?_⟩
  · exact (integral_congr_ae (heq.mono (fun _ h => congrArg (fun t : ℝ => t^2) h))).trans_le henergy
  · filter_upwards [heq,hlim] with z hz hl
    rw [hz]
    exact hl.2

end CircleDomainRigidity

end

end OAI
