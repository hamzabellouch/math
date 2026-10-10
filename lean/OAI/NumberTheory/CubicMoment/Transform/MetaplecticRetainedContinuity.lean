import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedEstimate

namespace OAI

/-! Continuity of the actual finite retained transform. The common
critical-line majorant proves it without a uniform-series assumption. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_metaplectic_kernel_integral (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (c : ℝ) {P : ℝ → ℂ} (hP : Continuous P)
    {B : ℝ} (hB : ∀ u, ‖P u‖ ≤ B) :
    Continuous (fun t : ℝ => ∫ τ : ℝ, metaplecticCriticalKernel ℓ W c P τ t) := by
  have hc : Continuous (fun z : ℝ × ℝ => metaplecticCriticalKernel ℓ W c P z.1 z.2) :=
    continuous_metaplecticCriticalKernel ℓ W hW hpos hsm c hP
  have hslice (τ : ℝ) : Continuous (fun t : ℝ => metaplecticCriticalKernel ℓ W c P τ t) := by
    have hx : Continuous (fun t : ℝ => (τ,t)) := continuous_const.prodMk continuous_id
    exact hc.comp (f := fun t : ℝ => (τ,t)) hx
  apply continuous_of_dominated
    (F := fun t τ : ℝ => metaplecticCriticalKernel ℓ W c P τ t) (μ := volume)
    (bound := fun τ : ℝ => ‖mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)‖*B)
  · intro t
    exact (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (fun τ => by
      rw [norm_metaplecticCriticalKernel]
      exact mul_le_mul_of_nonneg_left (hB (τ-t)) (_root_.norm_nonneg _))
  · exact (metaplectic_mellin_half_integrable W hW hpos hsm).norm.mul_const B
  · exact Filter.Eventually.of_forall hslice

lemma continuous_metaplectic_retained
    (a : Eisenstein → MetaplecticDualArgument → ℂ) {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A X : ℝ} (hA : 0 ≤ A) (hX : 0 < X) (J : ℝ)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A)) :
    Continuous (fun t : ℝ => ∑ nd ∈ metaplecticDualBall J,
      metaplecticDualTerm a r ℓ (fun x => W x*mellinPhase t x) A X nd) := by
  let P := fun u : ℝ => ∑ nd ∈ metaplecticDualBall J,
    metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro nd hnd
    apply continuous_const.mul
    unfold mellinPhase
    fun_prop
  have hB (u : ℝ) : ‖P u‖ ≤ ∑ nd ∈ metaplecticDualBall J,
      ‖metaplecticNormalizedDualCoefficient a r ℓ nd‖ := by
    calc
      _ ≤ ∑ nd ∈ metaplecticDualBall J,
        ‖metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase u (metaplecticDualNorm nd)‖ :=
          norm_sum_le _ _
      _ = _ := by simp only [norm_mul,mellinPhase_norm,mul_one]
  have hc := continuous_metaplectic_kernel_integral ℓ W hW hpos hsm
    ((2*Real.pi)^4*X/norm r^2) hP hB
  have he (t : ℝ) := metaplectic_retained_critical a hr ℓ W hW hpos hsm hA hX J t hm hp
  simp_rw [he]
  exact continuous_const.mul hc

lemma continuous_metaplectic_height_completed (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0 < X) :
    Continuous (metaplecticHeightCompleted r ℓ W X) := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  have hcut : ∀ x : ℝ, B < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hB x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self x]
  have he (t : ℝ) := metaplecticHeightCompleted_finite r ℓ W hX
    (le_refl (B*X)) hcut t
  change Continuous (fun t : ℝ => metaplecticHeightCompleted r ℓ W X t)
  simp_rw [he]
  apply continuous_finsetSum
  intro du hdu
  apply continuous_const.mul
  unfold mellinPhase
  fun_prop

lemma continuous_metaplectic_height_main (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (X : ℝ) :
    Continuous (fun t : ℝ => mellinPhase t X*
      metaplecticMain r ℓ (fun x => W x*mellinPhase t x) X) := by
  have hm := (smooth_mellin_entire W hW hpos hsm.continuous).continuous
  have hp : Continuous (fun t : ℝ => mellinPhase t X) := by
    unfold mellinPhase
    fun_prop
  by_cases hℓ : ℓ = 0
  · simp only [metaplecticMain,hℓ,ite_true,mellin_mul_phase]
    exact hp.mul (continuous_const.mul (hm.comp (by fun_prop)))
  · simp only [metaplecticMain,hℓ,ite_false,mul_zero]
    exact continuous_const

end CubicFirstMoment

end

end OAI
