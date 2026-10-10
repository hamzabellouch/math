import OAI.Geometry.RCD.Heat.GaussianGridComparison
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-! # From Gaussian midpoint comparison to hyperbolic comparison -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem gaussian_hyperbolic_comparison (u : ℝ → ℝ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hcq : c < q^2)
    (hu : UpperSemicontinuousOn u (Icc 0 1)) (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1)
    (hm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      Real.exp (-c*(x-y)^2/8)*(u x+u y)/2 ≤ u ((x+y)/2))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : hyperbolicChord q (u 0) (u 1) t ≤ u t := by
  let x := fun j : ℕ => (⌊t*((j+1:ℕ):ℝ)⌋₊:ℝ)/((j+1:ℕ):ℝ)
  have hjpos (j : ℕ) : 0 < ((j+1:ℕ):ℝ) := by positivity
  have hfloor (j : ℕ) : ⌊t*((j+1:ℕ):ℝ)⌋₊ ≤ j+1 := by
    apply Nat.floor_le_of_le
    exact (mul_le_mul_of_nonneg_right ht.2 (hjpos j).le).trans_eq (one_mul _)
  have hxmem (j : ℕ) : x j ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (hjpos j).le
    · exact (div_le_one (hjpos j)).mpr (by exact_mod_cast hfloor j)
  have hn : Tendsto (fun j : ℕ => ((j+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hx : Tendsto x atTop (𝓝 t) := (tendsto_nat_floor_mul_div_atTop ht.1).comp hn
  have hxw : Tendsto x atTop (𝓝[Icc (0:ℝ) 1] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,Filter.Eventually.of_forall hxmem⟩
  have hd : Tendsto (fun j : ℕ => 1/((j+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hgrid : ∀ᶠ j : ℕ in atTop, hyperbolicChord q (u 0) (u 1) (x j) ≤ u (x j) := by
    filter_upwards [hd.eventually (eventually_gaussian_cosh_comparison hc hcq)] with j hj
    exact gaussian_grid_comparison u hc hq hu0 hu1 hm (j+1) (by omega) hj _ (hfloor j)
  by_contra hbad
  have hlt : u t < hyperbolicChord q (u 0) (u 1) t := lt_of_not_ge hbad
  let a := (u t+hyperbolicChord q (u 0) (u 1) t)/2
  have hleft : u t < a := by dsimp [a]; linarith
  have hright : a < hyperbolicChord q (u 0) (u 1) t := by dsimp [a]; linarith
  have hub : ∀ᶠ j in atTop, u (x j) < a := hxw.eventually (hu t ht a hleft)
  have hlb : ∀ᶠ j in atTop, a < hyperbolicChord q (u 0) (u 1) (x j) :=
    ((continuous_hyperbolicChord q (u 0) (u 1)).tendsto t |>.comp hx).eventually (lt_mem_nhds hright)
  obtain ⟨j,hj,hb,ha⟩ := (hgrid.and (hub.and hlb)).exists
  exact (ha.trans_le hj).not_gt hb

end RegularPointCoordinates

end

end OAI
