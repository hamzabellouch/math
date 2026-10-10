import OAI.MeasureTheory.Falconer.Radial.CoarsePlateAffineBound
import OAI.MeasureTheory.Falconer.Estimates.CoarseFloorPowers
import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtSlab

namespace OAI

/-! # The all-radius directional slab estimate for each coarse filter -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

noncomputable def coarseDirectionalConstant {d : ℕ} (Q : DyadicCube d)
    (j₀ : ℕ) (b : ℝ) : ℝ :=
  coarseSlabConstant j₀ b*(2*max (Real.sqrt d*Q.side) 1)^b

theorem coarseDirectionalConstant_pos {d : ℕ} (Q : DyadicCube d) (j₀ : ℕ) (b : ℝ) :
    0 < coarseDirectionalConstant Q j₀ b := by
  apply mul_pos (coarseSlabConstant_pos j₀ b)
  apply Real.rpow_pos_of_pos
  have h := le_max_right (Real.sqrt d*Q.side) (1:ℝ)
  linarith

theorem coarse_filter_directional_bound {d : ℕ} (μ ρ : Measure (Space d))
    [IsProbabilityMeasure μ] (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (j₀ N : ℕ)
    {b ω : ℝ} (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hμ : μ ≤ ρ)
    (x w : Space d) (hw : ‖w‖ = 1) {r : ℝ} (hr : plateScale N ≤ r) (hr1 : r ≤ 1) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
      ENNReal.ofReal (coarseDirectionalConstant Q j₀ b*r^(ω*b)) := by
  let D := Real.sqrt d*Q.side
  have hr0 : 0 < r := (plateScale_pos N).trans_le hr
  have hm : μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
      μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale
      (fun j => 2*(plateScale j)^b) ∧ |inner ℝ w y-inner ℝ w x| ≤ D*r} := by
    apply measure_mono
    intro y hy
    refine ⟨hy.1,?_⟩
    have hnorm : ‖y-x‖ ≤ D := by
      simpa only [dist_eq_norm] using Q.dist_le hQ hy.1.1.2 hy.1.1.1
    have hs := normalized_direction_slab w y x hnorm hr0.le hy.2
    simpa only [abs_sub_comm] using hs
  apply hm.trans ((coarse_filter_affine_bound μ ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ hb hμ x w hw (D*r)).trans
    (ENNReal.ofReal_le_ofReal ?_))
  calc
    _ ≤ coarseSlabConstant j₀ b*((2*max D 1)^b*r^(ω*b)) :=
      mul_le_mul_of_nonneg_left (coarse_floor_radius_power N hω hω1 hb hr hr1 D)
        (coarseSlabConstant_pos j₀ b).le
    _ = _ := by dsimp [coarseDirectionalConstant,D]; ring

end Falconer

end OAI
