import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

open scoped Topology CStarAlgebra

def spectralRamp (θ s : ℝ) : ℝ := min 1 (max 0 ((s-θ)/θ))

lemma continuous_spectralRamp (θ : ℝ) : Continuous (spectralRamp θ) := by
  unfold spectralRamp
  fun_prop

lemma spectralRamp_nonneg (θ s : ℝ) : 0 ≤ spectralRamp θ s :=
  le_min zero_le_one (le_max_left _ _)

lemma spectralRamp_le_one (θ s : ℝ) : spectralRamp θ s ≤ 1 := min_le_left _ _

lemma spectralRamp_eq_zero {θ s : ℝ} (hθ : 0 < θ) (hs : s ≤ θ) :
    spectralRamp θ s = 0 := by
  unfold spectralRamp
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hθ.le)]
  exact min_eq_right zero_le_one

lemma spectralRamp_eq_one {θ s : ℝ} (hθ : 0 < θ) (hs : 2*θ ≤ s) :
    spectralRamp θ s = 1 := by
  unfold spectralRamp
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  rw [le_div_iff₀ hθ]
  linarith

lemma spectralRamp_coercive {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    θ*(spectralRamp θ s*spectralRamp θ s) ≤ spectralRamp θ s*s*spectralRamp θ s := by
  by_cases hs : s ≤ θ
  · rw [spectralRamp_eq_zero hθ hs]
    simp
  · have h : θ ≤ s := le_of_lt (lt_of_not_ge hs)
    nlinarith [mul_le_mul_of_nonneg_right h (mul_self_nonneg (spectralRamp θ s))]

lemma spectralRamp_dominates {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hzero : ∀ s, s ≤ 2*θ → f s = 0)
    (hbound : ∀ s, f s ≤ L) (s : ℝ) :
    f s ≤ L*(spectralRamp θ s*spectralRamp θ s) := by
  by_cases hs : s ≤ 2*θ
  · rw [hzero s hs]
    exact mul_nonneg hL (mul_self_nonneg _)
  · rw [spectralRamp_eq_one hθ (le_of_lt (lt_of_not_ge hs)), one_mul, mul_one]
    exact hbound s

section Algebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conjugate_perturbation_lower (x y z : A) (hx : IsSelfAdjoint x)
    (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) {δ : ℝ}
    (hclose : ‖x-y‖ ≤ δ) : z*x*z - δ • (z*z) ≤ z*y*z := by
  have hsq : 0 ≤ z*z := by simpa only [hz.star_eq] using star_mul_self_nonneg z
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul z (x - y) (hx.sub hy)
  rw [hz.star_eq] at h
  have h' : z*(x-y)*z ≤ δ • (z*z) := h.trans (smul_le_smul_of_nonneg_right hclose hsq)
  have he : z*(x-y)*z = z*x*z-z*y*z := by noncomm_ring
  rw [he] at h'
  exact sub_le_iff_le_add.mpr ((sub_le_iff_le_add.mp h').trans_eq (add_comm _ _))

lemma spectralRamp_algebra_coercive (x : A) (hx : 0 ≤ x) {θ : ℝ} (hθ : 0 < θ) :
    θ • (cfcₙ (spectralRamp θ) x*cfcₙ (spectralRamp θ) x) ≤
      cfcₙ (spectralRamp θ) x*x*cfcₙ (spectralRamp θ) x := by
  have hg := (continuous_spectralRamp θ).continuousOn (s := quasispectrum ℝ x)
  have hg0 : spectralRamp θ 0 = 0 := spectralRamp_eq_zero hθ hθ.le
  have hm := cfcₙ_mono (a := x) (fun s _ => spectralRamp_coercive hθ s)
    (by fun_prop) (by fun_prop) (by simp [hg0]) (by simp [hg0])
  rw [cfcₙ_const_mul θ (fun s => spectralRamp θ s*spectralRamp θ s) x
      (by fun_prop) (by simp [hg0]),
    cfcₙ_mul (spectralRamp θ) (spectralRamp θ) x hg hg0 hg hg0,
    cfcₙ_mul (fun s => spectralRamp θ s*s) (spectralRamp θ) x
      (by fun_prop) (by simp [hg0]) hg hg0,
    cfcₙ_mul (spectralRamp θ) (fun s : ℝ => s) x hg hg0 continuousOn_id rfl,
    cfcₙ_id' ℝ x hx.isSelfAdjoint] at hm
  exact hm

lemma spectralRamp_algebra_dominates (x : A) {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hzero : ∀ s, s ≤ 2*θ → f s = 0) (hbound : ∀ s, f s ≤ L) :
    cfcₙ f x ≤ L • (cfcₙ (spectralRamp θ) x*cfcₙ (spectralRamp θ) x) := by
  have hg := (continuous_spectralRamp θ).continuousOn (s := quasispectrum ℝ x)
  have hg0 : spectralRamp θ 0 = 0 := spectralRamp_eq_zero hθ hθ.le
  have hm := cfcₙ_mono (a := x) (fun s _ => spectralRamp_dominates hθ hL f hzero hbound s)
    hf.continuousOn (by fun_prop) hf0 (by simp [hg0])
  rw [cfcₙ_const_mul L (fun s => spectralRamp θ s*spectralRamp θ s) x
      (by fun_prop) (by simp [hg0]),
    cfcₙ_mul (spectralRamp θ) (spectralRamp θ) x hg hg0 hg hg0] at hm
  exact hm

lemma spectralRamp_domination (x y : A) (hx : 0 ≤ x) (hy : 0 ≤ y)
    {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L) (hclose : ‖y-x‖ ≤ θ/2)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hzero : ∀ s, s ≤ 2*θ → f s = 0) (hbound : ∀ s, f s ≤ L) :
    cfcₙ f x ≤ (2*L/θ) • (cfcₙ (spectralRamp θ) x*y*cfcₙ (spectralRamp θ) x) := by
  let z := cfcₙ (spectralRamp θ) x
  have hz : 0 ≤ z := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg θ s)
  have hclose' : ‖x-y‖ ≤ θ/2 := by rwa [norm_sub_rev]
  have hp := conjugate_perturbation_lower x y z hx.isSelfAdjoint hy.isSelfAdjoint hz.isSelfAdjoint hclose'
  have hp' : (θ/2) • (z*z) ≤ z*y*z := by
    have hco : θ • (z*z) ≤ z*x*z := spectralRamp_algebra_coercive x hx hθ
    calc
      (θ/2) • (z*z) = θ • (z*z) - (θ/2) • (z*z) := by
        rw [← sub_smul]; congr 1; ring
      _ ≤ z*x*z - (θ/2) • (z*z) := sub_le_sub_right hco _
      _ ≤ z*y*z := hp
  have hc : 0 ≤ 2*L/θ := by positivity
  calc
    cfcₙ f x ≤ L • (z*z) := spectralRamp_algebra_dominates x hθ hL f hf hf0 hzero hbound
    _ = (2*L/θ) • ((θ/2) • (z*z)) := by
      rw [smul_smul]
      congr 1
      field_simp
    _ ≤ (2*L/θ) • (z*y*z) := smul_le_smul_of_nonneg_left hp' hc

end Algebra

end WeakPureInfiniteness
end

end OAI
