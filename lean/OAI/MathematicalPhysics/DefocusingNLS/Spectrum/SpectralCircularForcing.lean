import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoefficientContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularCorrection

namespace OAI

/-! Bounded normalized forcing from the actual profile expansion error. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem exists_circularBounded (F : ℝ → E₄) (hF : Continuous F)
    (M : ℝ) (hFM : ∀ t, ‖F t‖ ≤ M) :
    ∃ r : CircularTailSpace, ∀ t, circularTailEvaluation r t=F t := by
  let r₁ : ℝ →ᵇ ℂ × ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (F t).1) hF.fst M (fun t => (norm_fst_le (F t)).trans (hFM t))
  let r₂ : ℝ →ᵇ ℂ × ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (F t).2) hF.snd M (fun t => (norm_snd_le (F t)).trans (hFM t))
  exact ⟨(r₁,r₂),fun _ => rfl⟩

theorem exists_circular_weighted_coefficient_error (νp νm η : ℂ) (m : ℕ)
    (M κ : ℝ) (q p : ℝ → ℂ) (hq : Continuous q) (hp : Continuous p)
    (hqM : ∀ t, ‖q t‖ ≤ M) (hpM : ∀ t, ‖p t‖ ≤ M)
    (e : ℝ →ᵇ ℂ) (Z : CircularTailSpace)
    (hqe : ∀ t, 0 ≤ t → q t-p t=(Real.exp (-κ*t) : ℂ)*e t) :
    ∃ r : CircularTailSpace, ∀ t, 0 ≤ t →
      circularTailEvaluation r t=Real.exp (κ*t) •
        (circularBoundedField νp νm η m (q t) (circularTailEvaluation Z t)-
         circularBoundedField νp νm η m (p t) (circularTailEvaluation Z t)) := by
  obtain ⟨K,hK,hLip⟩ := circularBoundedField_coefficient_lipschitz m M
  let F : ℝ → E₄ := fun t => Real.exp (κ*max t 0) •
    (circularBoundedField νp νm η m (q (max t 0)) (circularTailEvaluation Z (max t 0))-
     circularBoundedField νp νm η m (p (max t 0)) (circularTailEvaluation Z (max t 0)))
  have hmax : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  have hZ := (circularTailEvaluation_continuous Z).comp hmax
  have hexp : Continuous (fun t : ℝ => Real.exp (κ*max t 0)) := by fun_prop
  have hF : Continuous F :=
    hexp.smul
      (((circularBoundedField_continuous νp νm η m).comp ((hq.comp hmax).prodMk hZ)).sub
       ((circularBoundedField_continuous νp νm η m).comp ((hp.comp hmax).prodMk hZ)))
  have hbound : ∀ t, ‖F t‖ ≤ K*‖e‖*‖Z‖ := by
    intro t
    let s := max t 0
    have hs : 0 ≤ s := le_max_right t 0
    have he : Real.exp (κ*s)*Real.exp (-κ*s)=1 := by
      rw [← Real.exp_add]
      simp
    have hdiff : ‖q s-p s‖ ≤ Real.exp (-κ*s)*‖e‖ := by
      rw [hqe s hs,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (e.norm_coe_le_norm s) (Real.exp_nonneg _)
    change ‖Real.exp (κ*s) • (_ : E₄)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (κ*s)*(K*‖q s-p s‖*‖circularTailEvaluation Z s‖) :=
        mul_le_mul_of_nonneg_left (hLip νp νm η (q s) (p s) (hqM s) (hpM s) _)
          (Real.exp_nonneg _)
      _ ≤ Real.exp (κ*s)*(K*(Real.exp (-κ*s)*‖e‖)*‖Z‖) := by
        gcongr
        exact circularTailEvaluation_norm Z s
      _ = K*‖e‖*‖Z‖ := by
        calc
          _ = (Real.exp (κ*s)*Real.exp (-κ*s))*(K*‖e‖*‖Z‖) := by ring
          _ = _ := by rw [he,one_mul]
  obtain ⟨r,hr⟩ := exists_circularBounded F hF (K*‖e‖*‖Z‖) hbound
  refine ⟨r,?_⟩
  intro t ht
  simpa only [F,max_eq_left ht] using hr t

end DefocusingNLS

end OAI
