import OAI.Analysis.Mahler.HolomorphicRegularity
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology

section Schwarz
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A centered Schwarz bound with a uniform bound on values. -/
lemma fderiv_bound_of_ball_bound {f : E → F} {x : E} {R r C : ℝ}
    (hr : 0 < r) (hx : ‖x‖ + r ≤ R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : E) R, ‖f z‖ ≤ C) :
    ‖fderiv ℂ f x‖ ≤ 2*C/r := by
  have hsub : ball x r ⊆ ball (0 : E) R := by
    intro z hz
    have htri := norm_add_le (z-x) x
    have hdist : ‖z-x‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    rw [sub_add_cancel] at htri
    rw [mem_ball,dist_zero_right]
    linarith
  have hxin : x ∈ ball (0 : E) R := hsub (mem_ball_self hr)
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) _ hr
  intro z hz
  rw [mem_closedBall,dist_eq_norm]
  exact (norm_sub_le _ _).trans (by linarith [hbound z (hsub hz),hbound x hxin])

/-- Two nested Schwarz estimates give uniform first and second derivative
bounds on a fixed neighborhood of the unit sphere. -/
theorem two_derivative_bounds {f : E → F} {C : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 4))
    (hf' : DifferentiableOn ℂ (fderiv ℂ f) (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : E) 4, ‖f z‖ ≤ C) :
    ∀ z ∈ closedBall (0 : E) 2,
      ‖f z‖ ≤ C ∧ ‖fderiv ℂ f z‖ ≤ 2*C ∧
        ‖fderiv ℂ (fderiv ℂ f) z‖ ≤ 4*C := by
  have hfirst : ∀ z ∈ ball (0 : E) 3, ‖fderiv ℂ f z‖ ≤ 2*C := by
    intro z hz
    have hz' : ‖z‖ < 3 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [div_one] using fderiv_bound_of_ball_bound (r := 1) (by norm_num)
      (by linarith : ‖z‖+1 ≤ 4) hf hbound
  intro z hz
  have hz' : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hz3 : z ∈ ball (0 : E) 3 := by rw [mem_ball,dist_zero_right]; linarith
  refine ⟨hbound z (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4) hz3),hfirst z hz3,?_⟩
  have h := fderiv_bound_of_ball_bound (f := fderiv ℂ f) (r := 1) (by norm_num)
    (by linarith : ‖z‖+1 ≤ 3) (hf'.mono (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4))) hfirst
  nlinarith
end Schwarz

section Remainder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The punctured Taylor estimate yields a uniform O(epsilon) bound after
rescaling on any prescribed bounded ball. This includes the center. -/
theorem rescaled_remainder_bound {f : E → F} {m : ℕ} (hf0 : f 0 = 0)
    (hf : f =O[𝓝[≠] 0] (fun z : E => ‖z‖^(m+1))) {B : ℝ} (hB : 0 < B) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ z : E, ‖z‖ ≤ B → ‖(ε^m)⁻¹ • f (ε • z)‖ ≤ C*ε := by
  obtain ⟨c,hc,hcf⟩ := hf.exists_pos
  have hfull : IsBigOWith c (𝓝 (0 : E)) f (fun z : E => ‖z‖^(m+1)) := by
    have h := hcf.insert (by simp [hf0])
    have hs : insert (0 : E) ({0}ᶜ : Set E) = univ := by
      ext z
      simp
      tauto
    rw [hs,nhdsWithin_univ] at h
    exact h
  obtain ⟨r,hr,hrbound⟩ := Metric.eventually_nhds_iff.mp hfull.bound
  refine ⟨c*B^(m+1),by positivity,r/B,by positivity,?_⟩
  intro ε hε hεδ z hz
  have hzball : dist (ε • z) (0 : E) < r := by
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left hz hε.le).trans_lt ((lt_div_iff₀ hB).mp hεδ)
  have hb := hrbound hzball
  have hm : 0 < ε^m := pow_pos hε m
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (ε^m)⁻¹ * (c*‖ε • z‖^(m+1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm.le)
      simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hb
    _ ≤ (ε^m)⁻¹ * (c*(ε*B)^(m+1)) := by
      gcongr
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
      exact mul_le_mul_of_nonneg_left hz hε.le
    _ = c*B^(m+1)*ε := by
      rw [mul_pow,pow_succ ε m]
      field_simp
end Remainder

end MahlerRescaling

end OAI
