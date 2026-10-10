import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogWindowCost
import OAI.NumberTheory.CubicMoment.Estimates.LogSchwartzWeight
import OAI.NumberTheory.CubicMoment.Estimates.MellinPrimeControl

namespace OAI

/-! The actual smooth dyadic norm cutoff, with a polynomial bound on all
Mellin quantities needed in the prime contour argument. -/
noncomputable section
open Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

lemma primeLogWindow_norm {J : ℝ} (hJ : 0 ≤ J) (u : ℝ) : ‖primeLogWindow J u‖ ≤ 1 := by
  have hm : Real.smoothTransition (J*u) ≤ Real.smoothTransition (J*(u+Real.log 2)+1) := by
    apply Real.smoothTransition.monotone
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hp := Real.smoothTransition.le_one (J*(u+Real.log 2)+1)
  have hz := Real.smoothTransition.nonneg (J*u)
  rw [primeLogWindow,primeSmoothStep,primeSmoothStep,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hm)]
  linarith

lemma primeLogWindowSchwartz_support_two {J : ℝ} (hJ : 1 ≤ J) :
    ∀ u ∈ tsupport (primeLogWindowSchwartz J (by linarith) : ℝ → ℂ), |u| ≤ 2 :=
  fun _u hu => primeLogWindow_support_two hJ hu

def primeDyadicWeight (J : ℝ) (hJ : 1 ≤ J) : ℝ → ℂ :=
  logSchwartzWeight (primeLogWindowSchwartz J (by linarith))

lemma primeDyadicWeight_compact {J : ℝ} (hJ : 1 ≤ J) :
    HasCompactSupport (primeDyadicWeight J hJ) :=
  logSchwartzWeight_compact _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_positive_support {J : ℝ} (hJ : 1 ≤ J) :
    tsupport (primeDyadicWeight J hJ) ⊆ Ioi 0 :=
  logSchwartzWeight_positive_support _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_smooth {J : ℝ} (hJ : 1 ≤ J) :
    ContDiff ℝ ∞ (primeDyadicWeight J hJ) :=
  logSchwartzWeight_smooth _ (primeLogWindowSchwartz_support_two hJ)

lemma primeDyadicWeight_exp {J : ℝ} (hJ : 1 ≤ J) (u : ℝ) :
    primeDyadicWeight J hJ (Real.exp (-u))=primeLogWindow J u :=
  logSchwartzWeight_exp _ u

lemma primeDyadicWeight_one {J x : ℝ} (hJ : 1 ≤ J) (hx : 1 ≤ x ∧ x ≤ 2) :
    primeDyadicWeight J hJ x=1 := by
  have hxp : 0 < x := by linarith
  change (if 0 < x then primeLogWindow J (-Real.log x) else 0)=1
  rw [ite_eq_left hxp]
  apply primeLogWindow_one (by linarith)
  have hl0 := Real.log_nonneg hx.1
  have hl2 := Real.log_le_log hxp hx.2
  exact ⟨by linarith,by linarith⟩

lemma primeDyadicWeight_norm {J : ℝ} (hJ : 1 ≤ J) (x : ℝ) :
    ‖primeDyadicWeight J hJ x‖ ≤ 1 := by
  change ‖if 0 < x then primeLogWindow J (-Real.log x) else 0‖ ≤ 1
  split_ifs
  · exact primeLogWindow_norm (by linarith) _
  · norm_num

lemma PrimeMellinControl.mono {W : ℝ → ℂ} {D E : ℝ}
    (hD : PrimeMellinControl W D) (hDE : D ≤ E) : PrimeMellinControl W E :=
  ⟨hD.nonneg.trans hDE,fun σ hσ t => (hD.decay σ hσ t).trans hDE,
    fun σ hσ => (hD.mass σ hσ).trans hDE,fun σ hσ => (hD.moment σ hσ).trans hDE⟩

theorem primeDyadicWeight_mellin_control :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      PrimeMellinControl (primeDyadicWeight J hJ) (K*J^d) := by
  obtain ⟨I,C,hC,hcontrol⟩ := primeMellinControl_finite_seminorm (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨d,K,hK,hcost⟩ := primeLogWindow_finite_cost I
  refine ⟨d,C*K,mul_pos hC hK,?_⟩
  intro J hJ
  have hfun : (fun u : ℝ => primeDyadicWeight J hJ (Real.exp (-u)))=primeLogWindow J :=
    funext (primeDyadicWeight_exp hJ)
  have hc := hcontrol (primeDyadicWeight J hJ) (primeDyadicWeight_compact hJ)
    (primeDyadicWeight_positive_support hJ) (primeDyadicWeight_smooth hJ) (by
      rw [hfun]
      exact fun u hu => primeLogWindow_support_two hJ hu)
  have he := logSchwartzWeight_log_profile _ (primeLogWindowSchwartz_support_two hJ)
  change mellinLogSchwartz (primeDyadicWeight J hJ) _ _ _ 0=primeLogWindowSchwartz J _ at he
  rw [he] at hc
  apply hc.mono
  calc
    _ ≤ C*(K*J^d) := mul_le_mul_of_nonneg_left (hcost J hJ) hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
