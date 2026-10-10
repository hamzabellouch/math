import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialCorrection
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFreeUniqueness

namespace OAI

/-! The unitary circular gauge and uniqueness of a sufficiently rapidly decaying tail. -/

open Set
namespace DefocusingNLS
local notation "E₂" => ℂ × ℂ
local notation "E₄" => E₂ × E₂

noncomputable def circularGauge (t : ℝ) (z : E₄) : E₄ :=
  ((z.1.1,radialExteriorPhase 0 t*z.1.2),
   (z.2.1,star (radialExteriorPhase 0 t)*z.2.2))

theorem circularGauge_norm (t : ℝ) (z : E₄) : ‖circularGauge t z‖=‖z‖ := by
  simp only [circularGauge,Prod.norm_def,norm_mul,norm_star,radialExteriorPhase_norm,one_mul]

theorem circularGauge_hasDerivAt (Z : ℝ → E₄) (t : ℝ) (F : E₄)
    (hZ : HasDerivAt Z (circularLeadingField t (Z t)+F) t) :
    HasDerivAt (fun s => circularGauge s (Z s)) (circularGauge t F) t := by
  have hZp := (ContinuousLinearMap.fst ℝ E₂ E₂).hasFDerivAt.comp_hasDerivAt t hZ
  have hZm := (ContinuousLinearMap.snd ℝ E₂ E₂).hasFDerivAt.comp_hasDerivAt t hZ
  have hZp0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZp
  have hZp1 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZp
  have hZm0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZm
  have hZm1 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZm
  change HasDerivAt (fun s => (Z s).1.1) (0+F.1.1) t at hZp0
  change HasDerivAt (fun s => (Z s).1.2)
    (-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).1.2+F.1.2) t at hZp1
  change HasDerivAt (fun s => (Z s).2.1) (0+F.2.1) t at hZm0
  change HasDerivAt (fun s => (Z s).2.2)
    (Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2.2+F.2.2) t at hZm1
  have hp := radialExteriorPhase_second_hasDerivAt 0 t
  have hm : HasDerivAt (fun s => star (radialExteriorPhase 0 s))
      (-Complex.I*(Real.exp (2*t)/2 : ℝ)*star (radialExteriorPhase 0 t)) t := by
    apply hp.star.congr_deriv
    simp only [star_mul,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring
  apply ((hZp0.prodMk (hp.mul hZp1)).prodMk (hZm0.prodMk (hm.mul hZm1))).congr_deriv
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularGauge]
  all_goals ring

theorem circularLeadingField_sub (t : ℝ) (z w : E₄) :
    circularLeadingField t (z-w)=circularLeadingField t z-circularLeadingField t w := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [circularLeadingField,mul_sub]

theorem circular_fast_decay_zero (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M κ C T : ℝ) (q : ℝ → ℂ) (Z : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η m (q t) (Z t)) t)
    (hdec : ∀ t, T ≤ t → ‖Z t‖ ≤ C*Real.exp (-κ*t))
    (hκ : circularFieldBound νp νm η m M < κ) (t : ℝ) (ht : T ≤ t) : Z t=0 := by
  let W := fun s => circularGauge s (Z s)
  let W' := fun s => circularGauge s (circularBoundedField νp νm η m (q s) (Z s))
  have hd : ∀ s, T ≤ s → HasDerivAt W (W' s) s := by
    intro s hs
    exact circularGauge_hasDerivAt Z s _ (hZ s hs)
  have hb : ∀ s, T ≤ s → ‖W' s‖ ≤ circularFieldBound νp νm η m M*‖W s‖ := by
    intro s hs
    simpa only [W,W',circularGauge_norm] using
      circularBoundedField_norm νp νm η m hm M (q s) (hq s hs) (Z s)
  have he := eq_zero_of_fast_exponential_decay W W' (circularFieldBound νp νm η m M)
    κ C T (fun s hs => (hd s hs).continuousAt.continuousWithinAt) hd hb
    (fun s hs => by simpa only [W,circularGauge_norm] using hdec s hs) hκ t ht
  apply norm_eq_zero.mp
  rw [← circularGauge_norm t (Z t)]
  exact norm_eq_zero.mpr he

theorem circular_fast_decay_unique (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M κ C T : ℝ) (q : ℝ → ℂ) (Z W : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η m (q t) (Z t)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      (circularLeadingField t (W t)+circularBoundedField νp νm η m (q t) (W t)) t)
    (hdec : ∀ t, T ≤ t → ‖Z t-W t‖ ≤ C*Real.exp (-κ*t))
    (hκ : circularFieldBound νp νm η m M < κ) (t : ℝ) (ht : T ≤ t) : Z t=W t := by
  apply sub_eq_zero.mp
  apply circular_fast_decay_zero νp νm η m hm M κ C T q (fun s => Z s-W s) hq _ hdec hκ t ht
  intro s hs
  apply ((hZ s hs).sub (hW s hs)).congr_deriv
  rw [circularLeadingField_sub,circularBoundedField_sub]
  abel

theorem circular_zero_of_zero_at (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M T s : ℝ) (q : ℝ → ℂ) (Z : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η m (q t) (Z t)) t)
    (hz : Z s=0) (t : ℝ) (ht : T ≤ t) (hts : t ≤ s) : Z t=0 := by
  let W := fun r => circularGauge r (Z r)
  let W' := fun r => circularGauge r (circularBoundedField νp νm η m (q r) (Z r))
  have hd : ∀ r, T ≤ r → HasDerivAt W (W' r) r := by
    intro r hr
    exact circularGauge_hasDerivAt Z r _ (hZ r hr)
  have hb : ∀ r, T ≤ r → ‖W' r‖ ≤ circularFieldBound νp νm η m M*‖W r‖ := by
    intro r hr
    simpa only [W,W',circularGauge_norm] using
      circularBoundedField_norm νp νm η m hm M (q r) (hq r hr) (Z r)
  have he := norm_le_backward_gronwall W W' (circularFieldBound νp νm η m M) T t s
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt) hd hb ht hts
  have hwz : ‖W s‖=0 := by simp only [W,circularGauge_norm,hz,norm_zero]
  rw [hwz,zero_mul] at he
  apply norm_le_zero_iff.mp
  simpa only [W,circularGauge_norm] using he


end DefocusingNLS

end OAI
