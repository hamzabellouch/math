import OAI.Analysis.LipschitzHilbert.Trees.LineGridBMO
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Actual cell averages converge at every continuity point in the root.
Only this continuous-function specialization of differentiation is needed
for the finite smooth packet and variation functions. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

def withDepth (g : FiniteLineGrid) (N : ℕ) : FiniteLineGrid := {g with depth := N}

theorem cell_zero (g : FiniteLineGrid) : g.cell 0 0 = g.root := by
  simp only [cell, meshWidth, pow_zero, div_one, Nat.cast_zero, mul_zero,
    add_zero, zero_add, mul_one, root]

theorem average_zero_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {x : ℝ} (hx : x ∈ g.root) :
    g.average g.lineMeasure f 0 x = integralAverage g.lineMeasure f := by
  rw [g.average_eq_cellMean (i := 0) f hf (Nat.zero_le _) (by simp)
    (by simpa only [g.cell_zero] using hx), g.cellMean_eq_integralAverage, g.cell_zero]
  rfl

theorem average_close_of_mesh (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {n : ℕ} (hn : n ≤ g.depth)
    {x : ℝ} (hx : x ∈ g.root) {epsilon delta : ℝ}
    (hlocal : ∀ y, dist y x < delta → |f y - f x| ≤ epsilon)
    (hmesh : g.meshWidth n < delta) :
    |g.average g.lineMeasure f n x - f x| ≤ epsilon := by
  let i := (g.index n x).val
  have hi : i < g.branching ^ n := g.index_lt_level hn x
  have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
  have hfc : IntegrableOn f (g.cell n i) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root n hi))
  have hpoint : ∀ᵐ y ∂volume.restrict (g.cell n i), ‖f x - f y‖ ≤ epsilon := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hyr := g.cell_subset_root n hi hy
    have hiy := (g.index_eq_iff_mem_cell hn hyr i).mpr hy
    have heq : g.index n y = g.index n x := Fin.ext hiy
    have hd := g.same_index_distance hn hyr hx heq
    have hdist : dist y x < delta := by
      rw [Real.dist_eq]
      exact hd.trans_lt hmesh
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hlocal y hdist
  have h := norm_sub_mean_le (volume.restrict (g.cell n i)) f hfc
    (by rw [g.cell_mass]; exact g.meshWidth_pos n) (f x) epsilon hpoint
  rw [g.average_eq_cellMean f hf hn hi hxc, g.cellMean_eq_integralAverage]
  simpa only [integralAverage, Real.norm_eq_abs, abs_sub_comm] using h

theorem meshWidth_tendsto_zero (g : FiniteLineGrid) (hb : 1 < g.branching) :
    Tendsto g.meshWidth atTop (𝓝 0) := by
  change Tendsto (fun n => g.width / (g.branching : ℝ) ^ n) atTop (𝓝 0)
  have hbR : (1 : ℝ) < g.branching := by exact_mod_cast hb
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := (g.branching : ℝ)⁻¹) (by rw [abs_of_pos (inv_pos.mpr (by linarith))]; exact inv_lt_one_of_one_lt₀ hbR)
  have h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n)
      atTop (𝓝 (g.width * 0)) := tendsto_const_nhds.mul hpow
  simpa only [mul_zero, meshWidth, div_eq_mul_inv, inv_pow] using
    (h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n) atTop (𝓝 (g.width * 0)))

theorem average_tendsto_at_continuity (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    {x : ℝ} (hx : x ∈ g.root) (hcont : ContinuousAt f x) :
    Tendsto (fun N => (g.withDepth N).average (g.withDepth N).lineMeasure f N x)
      atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hlocal⟩ := Metric.continuousAt_iff.mp hcont (epsilon / 2) (by positivity)
  have hmesh := (tendsto_order.mp (g.meshWidth_tendsto_zero hb)).2 delta hdelta
  filter_upwards [hmesh] with N hN
  rw [Real.dist_eq]
  apply lt_of_le_of_lt ((g.withDepth N).average_close_of_mesh f hf le_rfl hx
    (fun y hy => (by simpa only [Real.dist_eq] using (hlocal hy).le)) hN)
  linarith

end LipschitzHilbert.FiniteLineGrid

end

end OAI
