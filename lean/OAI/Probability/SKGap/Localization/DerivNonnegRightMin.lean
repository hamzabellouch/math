import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
namespace SKGapCutoff

lemma deriv_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmin : ∀ᶠ t in 𝓝[>] (0:ℝ), f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [hmin, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr (le_of_lt htpos))

lemma hasDerivAt_norm_inverse_direction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {A : E →L[ℝ] F} {z v : E} {y : F}
    (hf : HasFDerivAt f A z) (hv : A v = y-f z) (hne : f z ≠ y) :
    HasDerivAt (fun t : ℝ => ‖f (z+t • v)-y‖) (-‖f z-y‖) 0 := by
  have hp : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hcomp : HasDerivAt (fun t : ℝ => f (z+t • v)-y) (-(f z-y)) 0 := by
    have hf' : HasFDerivAt f A (z+(0:ℝ) • v) := by simpa using hf
    convert (hf'.comp_hasDerivAt 0 hp).sub_const y using 1 <;> simp [hv]
  have hs := hcomp.norm_sq
  have hb : 0 < ‖f z-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs' : HasDerivAt (fun t : ℝ => ‖f (z+t • v)-y‖^2)
      (-2*‖f z-y‖^2) 0 := by
    simpa only [zero_smul, add_zero, inner_neg_right, real_inner_self_eq_norm_sq, mul_neg, neg_mul] using hs
  have hh := hs'.sqrt (by simpa using (sq_pos_of_pos hb).ne')
  convert hh using 1
  · funext t
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg (f z-y))]
    field_simp

theorem ball_subset_image_of_uniform_right_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (hf : Continuous f) (z₀ : E) {R a : ℝ}
    (hR : 0 < R) (_ha : 0 < a)
    (hder : ∀ z ∈ ball z₀ R, ∃ A : E →L[ℝ] F,
      HasFDerivAt f A z ∧ ∀ w : F, ∃ v : E, A v = w ∧ a*‖v‖ ≤ ‖w‖) :
    ball (f z₀) (a*R) ⊆ f '' ball z₀ R := by
  intro y hy
  have hd₀ : ‖f z₀-y‖ < a*R := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hc₀ : ‖f z₀-y‖/R < a := (div_lt_iff₀ hR).mpr hd₀
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hc₀
  have hc : 0 < c := (div_nonneg (norm_nonneg _) hR.le).trans_lt hc₁
  have hcR : ‖f z₀-y‖ < c*R := (div_lt_iff₀ hR).mp hc₁
  let ψ := fun z : E => ‖f z-y‖+c*‖z-z₀‖
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall z₀ R).exists_isMinOn
    (nonempty_closedBall.mpr hR.le) hψ.continuousOn
  have hbound : ψ z ≤ ‖f z₀-y‖ := by
    simpa [ψ] using hmin (mem_closedBall_self hR.le)
  have hzR : z ∈ ball z₀ R := by
    rw [mem_ball, dist_eq_norm]
    apply (mul_lt_mul_iff_right₀ hc).mp
    have hn := norm_nonneg (f z-y)
    dsimp [ψ] at hbound
    linarith
  by_cases he : f z = y
  · exact ⟨z, hzR, he⟩
  obtain ⟨A, hA, hsurj⟩ := hder z hzR
  obtain ⟨v, hv, hvnorm⟩ := hsurj (y-f z)
  rw [norm_sub_rev] at hvnorm
  let η : ℝ → ℝ := fun t => ‖f (z+t • v)-y‖+c*(‖z-z₀‖+t*‖v‖)
  have hη : HasDerivAt η (-‖f z-y‖+c*‖v‖) 0 := by
    apply (hasDerivAt_norm_inverse_direction hA hv he).add
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const ‖v‖).const_add ‖z-z₀‖).const_mul c
  have hloc : ∀ᶠ t in 𝓝 (0:ℝ), z+t • v ∈ closedBall z₀ R := by
    have hc' : ContinuousAt (fun t : ℝ => z+t • v) 0 := by fun_prop
    have hh := hc'.preimage_mem_nhds (isOpen_ball.mem_nhds (by simpa using hzR))
    filter_upwards [hh] with t ht
    exact ball_subset_closedBall ht
  have hminη : ∀ᶠ t in 𝓝[>] (0:ℝ), η 0 ≤ η t := by
    filter_upwards [hloc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    have hh := hmin ht
    have htri : ‖z+t • v-z₀‖ ≤ ‖z-z₀‖+t*‖v‖ := by
      calc
        _ = ‖(z-z₀)+t • v‖ := by congr 1; abel
        _ ≤ ‖z-z₀‖+‖t • v‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    dsimp [η]
    simp only [zero_smul, add_zero, zero_mul]
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htri hc.le))
  have hnonneg := deriv_nonneg_of_right_min hη hminη
  have hnormpos : 0 < ‖f z-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hvpos : 0 < ‖v‖ := by
    by_contra! h
    have hv0 : v=0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    simp [hv0] at hv
    exact he (sub_eq_zero.mp hv.symm).symm
  have hstrict : c*‖v‖ < a*‖v‖ := mul_lt_mul_of_pos_right hc₂ hvpos
  linarith

lemma injective_of_norm_lower {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {a : ℝ} (ha : 0 < a) (hA : ∀ x, a*‖x‖ ≤ ‖A x‖) :
    Function.Injective A := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := hA (x-y)
  rw [map_sub, hxy, sub_self, norm_zero] at hh
  nlinarith [norm_nonneg (x-y)]

lemma exists_right_inverse_of_adjoint_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ x, a*‖x‖ ≤ ‖A.adjoint x‖) :
    ∀ w : E, ∃ v : E, A v = w ∧ a*‖v‖ ≤ ‖w‖ := by
  have hBsurj : Function.Surjective A.adjoint :=
    (LinearMap.injective_iff_surjective (f := A.adjoint.toLinearMap)).mp
      (injective_of_norm_lower A.adjoint ha hA)
  have hAlower : ∀ x : E, a*‖x‖ ≤ ‖A x‖ := by
    intro x
    by_cases hx : x=0
    · simp [hx]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨u, hu⟩ := hBsurj x
    have hnorm : a*‖u‖ ≤ ‖x‖ := by simpa [hu] using hA u
    have hi : ‖x‖^2 ≤ ‖A x‖*‖u‖ := by
      calc
        _ = ⟪x, A.adjoint u⟫ := by rw [hu, real_inner_self_eq_norm_sq]
        _ = ⟪A x, u⟫ := A.adjoint_inner_right x u
        _ ≤ _ := real_inner_le_norm _ _
    have hc : (a*‖x‖)*‖x‖ ≤ ‖A x‖*‖x‖ := by
      calc
        _ = a*(‖x‖^2) := by ring
        _ ≤ a*(‖A x‖*‖u‖) := mul_le_mul_of_nonneg_left hi ha.le
        _ = ‖A x‖*(a*‖u‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    exact (mul_le_mul_iff_left₀ hxpos).mp hc
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp
      (injective_of_norm_lower A ha hAlower)
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  exact ⟨v, hv, hv ▸ hAlower v⟩

theorem ball_subset_image_of_adjoint_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (hf : Continuous f) (z₀ : E) {R a : ℝ}
    (hR : 0 < R) (ha : 0 < a)
    (hder : ∀ z ∈ ball z₀ R, ∃ A : E →L[ℝ] E,
      HasFDerivAt f A z ∧ ∀ u : E, a*‖u‖ ≤ ‖A.adjoint u‖) :
    ball (f z₀) (a*R) ⊆ f '' ball z₀ R := by
  apply ball_subset_image_of_uniform_right_inverse f hf z₀ hR ha
  intro z hz
  obtain ⟨A, hA, hnorm⟩ := hder z hz
  exact ⟨A, hA, exists_right_inverse_of_adjoint_lower A ha hnorm⟩

end SKGapCutoff

open scoped BigOperators
open ContinuousLinearMap

end

end OAI
