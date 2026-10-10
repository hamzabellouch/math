import OAI.Geometry.RCD.Heat.CompactHeatMeasure
import OAI.Geometry.RCD.Sobolev.BoundedLpSquare

namespace OAI

/-! # Compact continuous approximation preserving a uniform amplitude -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]

/-- A bounded L² class has uniformly bounded compact continuous approximants. -/
theorem exists_bounded_continuous_L2_approximation (f : Lp ℝ 2 μ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) :
    ∃ F : ℕ → C_c(X, ℝ), (∀ i x, |F i x| ≤ C) ∧
      Tendsto (fun i => compactTestToL2 μ (F i)) atTop (𝓝 f) := by
  have hex (i : ℕ) : ∃ F : C_c(X, ℝ),
      ‖compactTestToL2 μ F - f‖ ≤ 1 / ((i : ℝ) + 1) := by
    let ε := 1 / ((i : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨g, hgs, hge, hgc, hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ((ENNReal.ofReal_pos.mpr hε).ne')
    let F : C_c(X, ℝ) := ⟨⟨g, hgc⟩, hgs⟩
    have he : (fun x => (f - compactTestToL2 μ F) x) =ᵐ[μ] (fun x => f x - g x) := by
      filter_upwards [Lp.coeFn_sub f (compactTestToL2 μ F), compactTestToL2_coe μ F] with x hx hy
      rw [hx]
      change f x - compactTestToL2 μ F x = f x - g x
      rw [hy]
      rfl
    refine ⟨F, ?_⟩
    rw [norm_sub_rev, Lp.norm_def, eLpNorm_congr_ae he]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hge).trans_eq
      (ENNReal.toReal_ofReal hε.le)
  choose G hG using hex
  have hlim : Tendsto (fun i => compactTestToL2 μ (G i)) atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) hG tendsto_one_div_add_atTop_nhds_zero_nat
  let F (i : ℕ) : C_c(X, ℝ) :=
    ⟨⟨fun x => clipReal C (G i x), (clipReal_lipschitz C).continuous.comp (G i).continuous⟩,
      (G i).hasCompactSupport.comp_left (clipReal_zero C)⟩
  let P : Lp ℝ 2 μ → Lp ℝ 2 μ := (clipReal_lipschitz C).compLp (clipReal_zero C)
  have hPf : P f = f := by
    apply Lp.ext
    filter_upwards [(clipReal_lipschitz C).coeFn_compLp (clipReal_zero C) f, hf] with x hx hb
    exact hx.trans (clipReal_eq_self C hb)
  have hFG (i : ℕ) : compactTestToL2 μ (F i) = P (compactTestToL2 μ (G i)) := by
    apply Lp.ext
    filter_upwards [compactTestToL2_coe μ (F i), compactTestToL2_coe μ (G i),
      (clipReal_lipschitz C).coeFn_compLp (clipReal_zero C) (compactTestToL2 μ (G i))]
      with x hx hy hz
    rw [hx, hz]
    change clipReal C (G i x) = clipReal C (compactTestToL2 μ (G i) x)
    rw [hy]
  refine ⟨F, fun i x => clipReal_abs_le C (G i x), ?_⟩
  have hh := ((clipReal_lipschitz C).continuous_compLp (clipReal_zero C)).tendsto f |>.comp hlim
  change Tendsto (fun i => P (compactTestToL2 μ (G i))) atTop (𝓝 (P f)) at hh
  rw [hPf] at hh
  exact hh.congr' (Eventually.of_forall fun i => (hFG i).symm)

end RegularPointCoordinates

end

end OAI
