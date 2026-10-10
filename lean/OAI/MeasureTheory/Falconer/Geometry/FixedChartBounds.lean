import OAI.MeasureTheory.Falconer.Estimates.MixedComposition
import OAI.MeasureTheory.Falconer.Geometry.QuadraticChart

namespace OAI

/-! # Uniform finite derivative bounds for fixed quadratic geometry

Only compact sets inside the smooth chart are used. The chart need not
extend smoothly through its outer singularity.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_iteratedFDeriv_bound_at {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i f) K := by
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose A hA using fun i => hK.exists_bound_of_continuousOn (hc i)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  refine ⟨C,Finset.sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem norm_iteratedFDeriv_mul_le_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (k-i) g x‖ := by
  obtain ⟨U,hU,hxU,hfU⟩ := hf.contDiffOn' (by simp : (k : ℕ∞ω) ≤ ∞) (by simp)
  obtain ⟨V,hV,hxV,hgV⟩ := hg.contDiffOn' (by simp : (k : ℕ∞ω) ≤ ∞) (by simp)
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hxW : x ∈ W := ⟨hxU,hxV⟩
  have hfU' : ContDiffOn ℝ k f U := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hfU
  have hgV' : ContDiffOn ℝ k g V := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hgV
  have hfW : ContDiffOn ℝ k f W := hfU'.mono inter_subset_left
  have hgW : ContDiffOn ℝ k g W := hgV'.mono inter_subset_right
  have hh := norm_iteratedFDerivWithin_mul_le hfW hgW hW.uniqueDiffOn hxW (le_refl (k : ℕ∞ω))
  have hre (j : ℕ) (a : E → ℂ) : iteratedFDerivWithin ℝ j a W x = iteratedFDeriv ℝ j a x :=
    iteratedFDerivWithin_of_isOpen j hW hxW
  simpa only [hre] using hh

noncomputable def quadraticChartDensity (m : ℕ) {n : ℕ} (u : Space n) : ℂ :=
  ((Real.sqrt (1-‖u‖^2/4))^m : ℂ)

theorem quadraticChartDensity_contDiffAt (m : ℕ) {n : ℕ} {u : Space n}
    (hu : ‖u‖ < 2) : ContDiffAt ℝ ∞ (quadraticChartDensity m) u := by
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0 : ℝ) ≤ 2)).mpr hu
  apply ContDiffAt.pow
  exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
    ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
      (by nlinarith : 1-‖u‖^2/4 ≠ 0))

theorem fixed_quadratic_geometry_bounds (n m k : ℕ) :
    ∃ Q C : ℝ, 0 ≤ Q ∧ 0 ≤ C ∧ ∀ j ≤ k, ∀ u : Space n, ‖u‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j quadraticSpherePoint u‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ j (quadraticChartDensity m) u‖ ≤ C := by
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticSpherePoint_contDiffAt (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticChartDensity_contDiffAt m (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  refine ⟨Q,C,hQ,hC,?_⟩
  intro j hj u hu
  have hum : u ∈ closedBall (0 : Space n) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hu
  exact ⟨hQb j hj u hum,hCb j hj u hum⟩

end Falconer

end OAI
