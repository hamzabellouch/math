import Mathlib.Topology.MetricSpace.Thickening
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped Topology
noncomputable section

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
  {D : Set Coord} {m J K k0 : ℕ}

theorem LocalCompactWaveData.uniform_support_core (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) {Ω : Set Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∀ t : a.cover.Parameter × Fin 3,
        tsupport (a.beams.wave (n:ℝ) t) ⊆ C ∧
        ∀ x ∉ C, ∀ k : ℕ,
          iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (a.beams.wave (n:ℝ) t) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*a.beams.wave (n:ℝ) t z) x = 0 := by
  obtain ⟨C,hC,hDC,hCΩ⟩ := exists_compact_between hD hΩ hDΩ
  obtain ⟨ε,hε,hth⟩ := hD.exists_cthickening_subset_open isOpen_interior hDC
  have hsmall : ∀ᶠ n : ℕ in atTop, a.beams.R*(n:ℝ)^(-1/3:ℝ) < ε := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ) < ε)
    have ht : Tendsto (fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul a.beams.R
    exact ht.eventually (gt_mem_nhds hε)
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [a.estimates,hsmall] with n hn hnε
  intro t
  have hsup : tsupport (a.beams.wave (n:ℝ) t) ⊆ C := by
    intro x hx
    have hb := (norm_le_sourceEuclideanNorm (x-coverSourceCenter a.cover t.1)).trans
      ((hn t).2.2.2.1 hx)
    have hc : coverSourceCenter a.cover t.1 ∈ D := (a.cover.center t.1).property
    apply interior_subset (hth (mem_cthickening_of_dist_le x (coverSourceCenter a.cover t.1) ε D hc ?_))
    rw [dist_eq_norm]
    exact (hb.trans_lt hnε).le
  refine ⟨hsup,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hsup hz)) k

end
end Yau.Geometry

end OAI
