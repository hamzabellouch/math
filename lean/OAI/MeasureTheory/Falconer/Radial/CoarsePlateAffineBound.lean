import OAI.MeasureTheory.Falconer.Estimates.TruncatedDyadicBound
import OAI.MeasureTheory.Falconer.Radial.CoarsePlateFilter

namespace OAI

/-! # All-width affine slab bounds for the original coarse-filter fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def coarseSlabConstant (j₀ : ℕ) (b : ℝ) : ℝ :=
  max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b)

theorem coarseSlabConstant_pos (j₀ : ℕ) (b : ℝ) : 0 < coarseSlabConstant j₀ b :=
  (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)).trans_le (le_max_right _ _)

theorem coarse_filter_affine_bound {d : ℕ} (μ ρ : Measure (Space d))
    [IsProbabilityMeasure μ] (Q : DyadicCube d) (j₀ J : ℕ)
    {b : ℝ} (hb : 0 ≤ b) (hμ : μ ≤ ρ)
    (x w : Space d) (hw : ‖w‖ = 1) (r : ℝ) :
    μ {y | (x,y) ∈ coarsePlateFilter ρ Q j₀ J plateScale (fun j => 2*(plateScale j)^b) ∧
      |inner ℝ w y-inner ℝ w x| ≤ r} ≤
      ENNReal.ofReal (coarseSlabConstant j₀ b*(max r (plateScale J))^b) := by
  let f := fun r : ℝ => μ {y |
    (x,y) ∈ coarsePlateFilter ρ Q j₀ J plateScale (fun j => 2*(plateScale j)^b) ∧
      |inner ℝ w y-inner ℝ w x| ≤ r}
  apply truncated_dyadic_bound j₀ J f
    (fun r t hrt => measure_mono (fun _ hy => ⟨hy.1,hy.2.trans hrt⟩))
    (fun _ => prob_le_one) hb _ r
  intro j hj₀ hjJ
  exact coarsePlateFilter_fiber_slab_bound μ ρ Q j₀ J plateScale
    (fun j => 2*(plateScale j)^b) hμ (Finset.mem_Icc.mpr ⟨hj₀,hjJ⟩)
    x w (inner ℝ w x) hw (by simpa only [sub_self,abs_zero] using (plateScale_pos j).le)

end Falconer

end OAI
