import OAI.NumberTheory.CubicMoment.Estimates.SmallTwistSmoothMoment

namespace OAI

/-! Logarithmic full factors are exact linear combinations of two smooth
weights. No logarithmic coefficient is silently discarded. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def logSmoothWeight (W : ℝ → ℂ) (x : ℝ) : ℂ := (Real.log x:ℂ)*W x

lemma logSmoothWeight_compact {W : ℝ → ℂ} (hW : HasCompactSupport W) :
    HasCompactSupport (logSmoothWeight W) :=
  hW.mul_left (f := fun x : ℝ => (Real.log x:ℂ))

lemma logSmoothWeight_positive {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0) :
    tsupport (logSmoothWeight W) ⊆ Ioi 0 := tsupport_mul_subset_right.trans hpos

lemma logSmoothWeight_smooth {W : ℝ → ℂ} (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (logSmoothWeight W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0:ℝ) ∉ tsupport W := fun h => (lt_irrefl (0:ℝ)) (hpos h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change W y = 0 at hy
    simp only [logSmoothWeight,hy,mul_zero]
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hsm.contDiffAt

lemma primary_weighted_smooth_finite (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) :
    (∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0) =
      ∑ a ∈ primaryElementBall (B*Z), c a*W (norm a/Z) := by
  calc
    _ = ∑ a ∈ primaryElementBall (B*Z), if primary a then c a*W (norm a/Z) else 0 := by
      apply tsum_eq_sum
      intro a ha
      by_cases hprim : primary a
      · have hN : B*Z < norm a := lt_of_not_ge (fun h => ha (mem_primaryElementBall.mpr ⟨hprim,h⟩))
        rw [ite_eq_left hprim,hW _ ((lt_div_iff₀ hZ).mpr hN),mul_zero]
      · rw [ite_eq_right hprim]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [ite_eq_left (mem_primaryElementBall.mp ha).1]

 theorem primary_log_smooth_decomposition (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' a : Eisenstein, if primary a then
      (Real.log (norm a):ℂ)*c a*W (norm a/Z) else 0) =
      (Real.log Z:ℂ)*(∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0)+
      ∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0 := by
  obtain ⟨B,_,hB⟩ := compactSupport_upper_cutoff W hW
  have hBlog (x : ℝ) (hx : B < x) : logSmoothWeight W x = 0 := by
    rw [logSmoothWeight,hB x hx,mul_zero]
  rw [primary_weighted_smooth_finite _ W hZ hB,
    primary_weighted_smooth_finite c W hZ hB,
    primary_weighted_smooth_finite c (logSmoothWeight W) hZ hBlog,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hn : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp ha).1)
  have hlog : Real.log (norm a) = Real.log Z+Real.log (norm a/Z) := by
    rw [Real.log_div hn.ne' hZ.ne']
    ring
  rw [hlog,Complex.ofReal_add,logSmoothWeight]
  ring

lemma primary_log_smooth_sq_le (c : Eisenstein → ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    ‖∑' a : Eisenstein, if primary a then
      (Real.log (norm a):ℂ)*c a*W (norm a/Z) else 0‖^2 ≤
      2*(Real.log Z)^2*‖∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0‖^2+
      2*‖∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0‖^2 := by
  rw [primary_log_smooth_decomposition c W hW hZ]
  let u : ℂ := ∑' a : Eisenstein, if primary a then c a*W (norm a/Z) else 0
  let v : ℂ := ∑' a : Eisenstein, if primary a then c a*logSmoothWeight W (norm a/Z) else 0
  change ‖(Real.log Z:ℂ)*u+v‖^2 ≤ 2*(Real.log Z)^2*‖u‖^2+2*‖v‖^2
  have ht := norm_add_le ((Real.log Z:ℂ)*u) v
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] at ht
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2
  nlinarith [sq_nonneg (|Real.log Z| * ‖u‖-‖v‖),sq_abs (Real.log Z)]

end CubicFirstMoment

end

end OAI
