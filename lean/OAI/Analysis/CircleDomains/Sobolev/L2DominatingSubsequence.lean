import OAI.Analysis.CircleDomains.Sobolev.L2Series

namespace OAI

/-! Strong L² convergence admits a cofinal subsequence with one L²
pointwise majorant. This will pass smooth line payments to a continuous
Sobolev limit without assuming an ACL representative theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_dominating_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (P : X → ℝ), Tendsto σ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧ (∀ᵐ x ∂μ, ∀ n, |f (σ n) x| ≤ P x) := by
  let δ := fun n : ℕ => (1/2:ℝ)^n
  have hδ (n : ℕ) : 0 < δ n := pow_pos (by norm_num) n
  have hδs : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n => (eLpNorm (fun x => f n x-g x) 2 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
  have hchoose (n : ℕ) : ∃ k, n ≤ k ∧ (eLpNorm (fun x => f k x-g x) 2 μ).toReal ≤ δ n := by
    obtain ⟨k,hk,hke⟩ := ((eventually_ge_atTop n).and (ht.eventually (gt_mem_nhds (hδ n)))).exists
    exact ⟨k,hk,hke.le⟩
  choose σ hσ hb using hchoose
  have hσt : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  let e := fun n x => f (σ n) x-g x
  have he (n : ℕ) : MemLp (e n) 2 μ := (hf _).sub hg
  have hes : Summable (fun n => (eLpNorm (e n) 2 μ).toReal) :=
    hδs.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hb
  have hef : (∑' n, eLpNorm (e n) 2 μ) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hδs.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (he n).ne_top]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hser := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) hef
  have hn : Summable (fun n => (eLpNorm (fun x => ‖e n x‖) 2 μ).toReal) := by
    simpa only [eLpNorm_norm _ (he _).aestronglyMeasurable] using hes
  have hsum := (l2_series_of_summable_norms (fun n x => ‖e n x‖) (fun n => (he n).norm) hn).1
  let Q := fun x => ‖g x‖+∑' n, ‖e n x‖
  have hQ : MemLp Q 2 μ := hg.norm.add hsum
  have hQ0 (x : X) : 0 ≤ Q x := add_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))
  let P := fun x => max (hQ.aestronglyMeasurable.mk Q x) 0
  have hPQ : P =ᵐ[μ] Q := by
    filter_upwards [hQ.aestronglyMeasurable.ae_eq_mk] with x hx
    change max (hQ.aestronglyMeasurable.mk Q x) 0 = Q x
    rw [← hx,max_eq_left (hQ0 x)]
  refine ⟨σ,P,hσt,hQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hQ.ae_eq hPQ.symm,?_⟩
  filter_upwards [hPQ,hser] with x hx hxs
  intro n
  rw [hx]
  have heq : f (σ n) x = g x+e n x := by dsimp only [e]; ring
  calc
    _ = ‖f (σ n) x‖ := Real.norm_eq_abs _ |>.symm
    _ ≤ ‖g x‖+‖e n x‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ Q x := by
      dsimp only [Q]
      exact add_le_add_right (hxs.le_tsum n (fun _ _ => norm_nonneg _)) _

end CircleDomainRigidity

end

end OAI
