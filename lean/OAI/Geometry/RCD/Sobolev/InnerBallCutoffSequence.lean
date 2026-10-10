import OAI.Geometry.RCD.Sobolev.NestedBallCutoff
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! # Continuous inner approximations to a ball indicator -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem inner_ball_lipschitz_cutoff_sequence (p : X) {R : ℝ} (hR : 0<R) :
    ∃ χ : ℕ → X →ᵇ ℝ, ∃ L : ℕ → ℝ≥0,
      (∀ m, LipschitzWith (L m) (χ m)) ∧
      (∀ m x, 0≤χ m x ∧ χ m x≤1) ∧
      (∀ m x, x∉ball p R → χ m x=0) ∧
      ∀ x, Tendsto (fun m => χ m x) atTop
        (𝓝 ((ball p R).indicator (fun _ => (1:ℝ)) x)) := by
  let T : ℕ → ℝ := fun m => R*(1-1/((m+2:ℕ):ℝ))
  have hTR (m : ℕ) : T m<R := by
    have hd : 0<1/((m+2:ℕ):ℝ) := by positivity
    dsimp only [T]
    nlinarith
  have hTlim : Tendsto T atTop (𝓝 R) := by
    have hd : Tendsto (fun m : ℕ => 1/((m+2:ℕ):ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
    simpa only [sub_zero,mul_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hd).const_mul R
  let χ : ℕ → X →ᵇ ℝ := fun m =>
    ⟨⟨nestedBallCutoff p (T m) R,(nestedBallCutoff_lipschitz p (hTR m)).continuous⟩,
      ⟨2,fun x y => by
        rw [Real.dist_eq]
        obtain ⟨hx0,hx1⟩ := nestedBallCutoff_bounds p (T m) R x
        obtain ⟨hy0,hy1⟩ := nestedBallCutoff_bounds p (T m) R y
        exact abs_le.mpr ⟨by linarith,by linarith⟩⟩⟩
  let L : ℕ → ℝ≥0 := fun m => ⟨(R-T m)⁻¹,inv_nonneg.mpr (sub_pos.mpr (hTR m)).le⟩
  refine ⟨χ,L,fun m => nestedBallCutoff_lipschitz p (hTR m),fun m x => nestedBallCutoff_bounds p (T m) R x,?_,?_⟩
  · intro m x hx
    exact nestedBallCutoff_eq_zero p (hTR m) (by
      simpa only [mem_ball,not_lt,dist_comm] using hx)
  · intro x
    by_cases hx : x∈ball p R
    · have hd : dist p x<R := by simpa only [mem_ball,dist_comm] using hx
      have he : ∀ᶠ m in atTop, χ m x=1 := by
        filter_upwards [hTlim.eventually (Ioi_mem_nhds hd)] with m hm
        exact nestedBallCutoff_eq_one p (hTR m) hm.le
      rw [indicator_of_mem hx]
      exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
    · have he (m : ℕ) : χ m x=0 := nestedBallCutoff_eq_zero p (hTR m)
        (by simpa only [mem_ball,not_lt,dist_comm] using hx)
      simp only [he,indicator_of_notMem hx]
      exact tendsto_const_nhds


theorem inner_ball_cutoff_sequence (p : X) {R : ℝ} (hR : 0<R) :
    ∃ χ : ℕ → X →ᵇ ℝ,
      (∀ m x, 0≤χ m x ∧ χ m x≤1) ∧
      (∀ m x, x∉ball p R → χ m x=0) ∧
      ∀ x, Tendsto (fun m => χ m x) atTop
        (𝓝 ((ball p R).indicator (fun _ => (1:ℝ)) x)) := by
  obtain ⟨χ,_,_,hb,hz,hl⟩ := inner_ball_lipschitz_cutoff_sequence p hR
  exact ⟨χ,hb,hz,hl⟩

end RegularPointCoordinates

end

end OAI
