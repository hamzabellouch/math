import Mathlib
import OAI.Geometry.CAT0Fillings.Sobolev.BrezisLieb
import OAI.Geometry.CAT0Fillings.Sobolev.CriticalNorm

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma criticalMass_defect (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 1 ≤ p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ)
    {u : ℕ → H} {v : H} (hu : ∀ j, criticalNorm I p (u j) = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (I (u j)) x) atTop (𝓝 ((I v) x))) :
    Tendsto (fun j => criticalMass I p (u j-v)) atTop (𝓝 (1-criticalMass I p v)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hf (j : ℕ) := criticalMass_integrable I hp0 (u j) (hm (u j))
  have hg := criticalMass_integrable I hp0 v (hm v)
  have hz (j : ℕ) : Integrable (fun x => |(I (u j)) x-(I v) x|^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,Pi.sub_apply] using
      ((hm (u j)).sub (hm v)).integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hb (j : ℕ) : ∫ x, |(I (u j)) x-(I v) x|^p ∂μ ≤ (1+criticalNorm I p v)^p := by
    rw [←criticalMass_sub I p (u j) v,criticalMass_eq I hp0]
    apply Real.rpow_le_rpow (criticalNorm_nonneg I p _) _ hp0.le
    dsimp [criticalNorm]
    rw [map_sub,lpNorm_congr_ae (Lp.coeFn_sub (I (u j)) (I v)) _]
    have hh := lpNorm_sub_le (hm (u j)) hpe (g := I v)
    simpa only [show lpNorm (I (u j)) (ENNReal.ofReal p) μ = 1 from hu j] using hh
  have hh := brezis_lieb_splitting hp0 (fun j => (I (u j) : α → ℝ)) (I v)
    hf hg hz hlim ((1+criticalNorm I p v)^p) hb
  have he (j : ℕ) : (∫ x, |(I (u j)) x|^p ∂μ) = 1 := by
    change criticalMass I p (u j) = 1
    rw [criticalMass_eq I hp0,hu j,Real.one_rpow]
  simp only [he,←criticalMass_sub] at hh
  have hd := ((tendsto_const_nhds (x := (1:ℝ))).sub hh).sub_const (criticalMass I p v)
  convert hd using 1
  · ext j
    dsimp [criticalMass]
    ring
  · simp

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_inner_weak_subsequence [CompleteSpace E] [SeparableSpace E]
    (u : ℕ → E) (M : ℝ) (hM : ∀ j, ‖u j‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ w : E, Tendsto (fun j => inner ℝ (u (s j)) w) atTop (𝓝 (inner ℝ v w)) := by
  let f : ℕ → WeakDual ℝ E := fun j => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u j))
  have hf : ∀ j, f j ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) M := by
    intro j
    simpa [f,mem_closedBall,dist_zero_right] using hM j
  obtain ⟨v,hv,s,hs,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hf
  let w := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual v)
  refine ⟨w,?_,s,hs,fun x => ?_⟩
  · have hw := (InnerProductSpace.toDual ℝ E).symm.norm_map (WeakDual.toStrongDual v)
    rw [hw]
    simpa only [mem_preimage,mem_closedBall,dist_zero_right] using hv
  · have hh := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hlim) x
    change Tendsto (fun j => inner ℝ (u (s j)) x) atTop (𝓝 ((WeakDual.toStrongDual v) x)) at hh
    simpa only [w,InnerProductSpace.toDual_symm_apply] using hh

lemma norm_le_of_inner_tendsto [CompleteSpace E] [SeparableSpace E]
    {u : ℕ → E} {v : E} {M : ℝ}
    (hM : ∀ j, ‖u j‖ ≤ M)
    (h : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w))) :
    ‖v‖ ≤ M := by
  by_cases hv : v = 0
  · subst v
    simpa using (norm_nonneg (u 0)).trans (hM 0)
  have hh : ‖v‖^2 ≤ M*‖v‖ := by
    have hi := le_of_tendsto' (h v) (fun j => (real_inner_le_norm (u j) v).trans
      (mul_le_mul_of_nonneg_right (hM j) (norm_nonneg _)))
    simpa only [real_inner_self_eq_norm_sq] using hi
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

end CAT0Fillings.AnalyticMinimizer
end

end OAI
