import OAI.NumberTheory.CubicMoment.Estimates.PrimeCutoffDerivative
import OAI.NumberTheory.CubicMoment.Estimates.PrimeWeightVariation
import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeSW

namespace OAI

/-! Actual cutoff weights on a free long prime. Their variation depends
on its dyadic ratio and Mellin height, not on the cutoff scales. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma radial_mellin_interval_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {P R a b M D : ℝ} (hP : 0 < P) (_hR : 1 ≤ R) (ha : P ≤ a)
    (hab : a ≤ b) (hb : b ≤ R*P) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w t*mellinPhase u t
    (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc a b) ∧
    ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|) := by
  dsimp only
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := fun _ ht => hP.trans_le (ha.trans ht.1)
  have hs : ContDiffOn ℝ ∞ (fun t => w t*mellinPhase u t) (Ioi 0) := by
    simpa only [div_one] using contDiffOn_rescaled_mellin hw 1 u
  have hd : ContinuousOn (deriv (fun t => w t*mellinPhase u t)) (Icc a b) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hs t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by norm_num)
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖‖deriv (fun t => w t*mellinPhase u t) t‖‖ ≤ (D+M*|u|)/P := by
    rw [uIoc_of_le hab] at ht
    have htP : P ≤ t := ha.trans ht.1.le
    have ht0 : 0 < t := hP.trans_le htP
    rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
    have hder := norm_deriv_weighted_mellinPhase
      ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt) u ht0
    have hdw : ‖deriv w t‖ ≤ D/t := (le_div_iff₀ ht0).mpr (hwd t ht0)
    calc
      _ ≤ D/t+M*(|u|/t) := hder.trans (add_le_add hdw
        (mul_le_mul_of_nonneg_right (hwm t) (div_nonneg (abs_nonneg _) ht0.le)))
      _ = (D+M*|u|)/t := by ring
      _ ≤ (D+M*|u|)/P := div_le_div_of_nonneg_left
        (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP htP
  have hint : (∫ t in Ioc a b, ‖deriv (fun t => w t*mellinPhase u t) t‖) ≤
      (R-1)*(D+M*|u|) := by
    rw [←intervalIntegral.integral_of_le hab]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    have hn : 0 ≤ ∫ t in a..b, ‖deriv (fun t => w t*mellinPhase u t) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    apply hi.trans
    calc
      (D+M*|u|)/P*(b-a) ≤ (D+M*|u|)/P*((R-1)*P) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (div_nonneg
          (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hP.le)
      _ = (R-1)*(D+M*|u|) := by field_simp
  have hnorm (x : ℝ) : ‖w x*mellinPhase u x‖ ≤ M := by
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm x
  linarith [hnorm a,hnorm b]

lemma primeDetectorCutoff_rescaled_smooth (c : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => (primeDetectorCutoff (t/c):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (primeDetectorCutoff_smooth.comp (contDiff_id.div_const c))

lemma primeDetectorCutoff_rescaled_norm (c t : ℝ) :
    ‖(primeDetectorCutoff (t/c):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (primeDetectorCutoff_nonneg _)]
  exact primeDetectorCutoff_le_one _

lemma primeDetectorCutoff_rescaled_deriv {D : ℝ}
    (hD : ∀ x : ℝ, 0 < x → |deriv primeDetectorCutoff x| * x ≤ D)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ‖deriv (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ)) t‖*t ≤ D := by
  have hd := (((primeDetectorCutoff_smooth.differentiable (by norm_num)).differentiableAt
    (x := t/c)).hasDerivAt.comp t ((hasDerivAt_id t).div_const c)).ofReal_comp
  change HasDerivAt (fun x : ℝ => (primeDetectorCutoff (x/c):ℂ))
    ((deriv primeDetectorCutoff (t/c)*(1/c):ℝ):ℂ) t at hd
  rw [hd.deriv,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos zero_lt_one hc)]
  convert hD (t/c) (div_pos ht hc) using 1; ring

/-- The same constant works for every cutoff scale. This is the actual
selected-bin prime weight, including any permitted norm twist. -/
theorem long_prime_cutoff_variation :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (c P R a b u : ℝ), 0 < c → 0 < P → 1 ≤ R →
      P ≤ a → a ≤ b → b ≤ R*P →
      let f := fun t => (primeDetectorCutoff (t/c):ℂ)*mellinPhase u t
      (∀ t ∈ Icc a b, DifferentiableAt ℝ f t) ∧
      IntegrableOn (deriv f) (Icc a b) ∧
      ‖f a‖+‖f b‖+(∫ t in Ioc a b, ‖deriv f t‖) ≤ 2+(R-1)*(D+|u|) := by
  obtain ⟨D,hD,hder⟩ := primeDetectorCutoff_radial_deriv_bound
  refine ⟨D,hD,?_⟩
  intro c P R a b u hc hP hR ha hab hb
  simpa only [mul_one,one_mul] using radial_mellin_interval_variation
    (primeDetectorCutoff_rescaled_smooth c) hP hR ha hab hb zero_le_one hD
    (primeDetectorCutoff_rescaled_norm c) (fun t ht => primeDetectorCutoff_rescaled_deriv
      hder hc ht) u

end CubicFirstMoment

end

end OAI
