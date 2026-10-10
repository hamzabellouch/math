import OAI.Analysis.CircleDomains.Topology.RetainedJordanConvergence
import OAI.Analysis.CircleDomains.Topology.PhysicalCollarCoordinates

namespace OAI

/-! Uniform convergence on a source circuit gives a vanishing numerical
error bound. No regularity of the finitely many early models is needed. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_circuit_uniform_error
    (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : TendstoUniformlyOn f g atTop (Icc (0 : ℝ) 1)) :
    ∃ e : ℕ → ℝ, (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) ≤ e n := by
  classical
  let D (n : ℕ) := (fun t => dist (f n t) (g t)) '' Icc (0 : ℝ) 1
  have hD (n) : (D n).Nonempty := ⟨dist (f n 0) (g 0), 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  let e (n : ℕ) := if h : BddAbove (D n) then sSup (D n) else 0
  have he (n) : 0 ≤ e n := by
    by_cases h : BddAbove (D n)
    · exact (dist_nonneg : 0 ≤ dist (f n 0) (g 0)).trans
        (by simp only [e, dite_eq_left h]; exact le_csSup h ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
    · simp only [e, dite_eq_right h, le_refl]
  have hε (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) < δ := by
    simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hf δ hδ)
  have hbounded {n : ℕ} {δ : ℝ}
      (h : ∀ t ∈ Icc (0 : ℝ) 1, dist (f n t) (g t) < δ) : BddAbove (D n) := by
    refine ⟨δ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (h t ht).le
  refine ⟨e, he, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hε (δ / 2) (half_pos hδ)] with n hn
    have hnB := hbounded hn
    have hle : e n ≤ δ / 2 := by
      simp only [e, dite_eq_left hnB]
      exact csSup_le (hD n) (by rintro _ ⟨t, ht, rfl⟩; exact (hn t ht).le)
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (he n)] using
      (hle.trans_lt (half_lt_self hδ))
  · filter_upwards [hε 1 zero_lt_one] with n hn t ht
    simp only [e, dite_eq_left (hbounded hn)]
    exact le_csSup (hbounded hn) ⟨t, ht, rfl⟩

 theorem tendstoUniformlyOn_retained_circuit
    (f : ℕ → Sphere → Sphere) (F : ℂ → ℂ) {G : Set Sphere}
    (hf : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere))) F atTop
      (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    TendstoUniformlyOn (fun n t => finiteCoord (f n (γ t : Sphere))) (F ∘ γ) atTop
      (Icc (0 : ℝ) 1) := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
  exact hf.comp γ (fun t _ => hG (mem_image_of_mem _ (hγ.mem_frontier t)))
    hγ.smooth.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
