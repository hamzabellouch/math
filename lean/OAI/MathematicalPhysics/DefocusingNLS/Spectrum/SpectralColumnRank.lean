import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnIndependence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularUniqueness

namespace OAI

/-! The normalized outgoing columns remain independent at each matching point. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circular_forward_zero (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M T s : ℝ) (q : ℝ → ℂ) (Z : ℝ → E₄)
    (hq : ∀ t, T ≤ t → ‖q t‖ ≤ M)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η m (q t) (Z t)) t)
    (hs : T ≤ s) (hz : Z s=0) (t : ℝ) (hst : s ≤ t) : Z t=0 := by
  let W := fun r => circularGauge r (Z r)
  let W' := fun r => circularGauge r (circularBoundedField νp νm η m (q r) (Z r))
  let B := circularFieldBound νp νm η m M
  have hd : ∀ r, T ≤ r → HasDerivAt W (W' r) r := by
    intro r hr
    exact circularGauge_hasDerivAt Z r _ (hZ r hr)
  have hb : ∀ r, T ≤ r → ‖W' r‖ ≤ B*‖W r‖ := by
    intro r hr
    simpa only [W,W',circularGauge_norm] using
      circularBoundedField_norm νp νm η m hm M (q r) (hq r hr) (Z r)
  have hc : ContinuousOn W (Icc s t) := fun r hr =>
    (hd r (hs.trans hr.1)).continuousAt.continuousWithinAt
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := B) (ε := 0) hc
    (fun r hr => (hd r (hs.trans hr.1)).hasDerivWithinAt)
    (show ‖W s‖ ≤ 0 by simp only [W,circularGauge_norm,hz,norm_zero,le_refl])
    (fun r hr => by simpa only [add_zero] using hb r (hs.trans hr.1)) t ⟨hst,le_rfl⟩
  have hg : gronwallBound 0 B 0 (t-s)=0 := by
    by_cases hB : B=0 <;> simp [gronwallBound,hB]
  rw [hg] at h
  apply norm_le_zero_iff.mp
  simpa only [W,circularGauge_norm] using h

theorem circularLeadingField_smul (t : ℝ) (a : ℂ) (z : E₄) :
    circularLeadingField t (a • z)=a • circularLeadingField t z := by
  apply Prod.ext <;> apply Prod.ext <;> simp [circularLeadingField,smul_eq_mul,mul_left_comm]

theorem circularBoundedField_smul (νp νm η : ℂ) (m : ℕ) (q a : ℂ) (z : E₄) :
    circularBoundedField νp νm η m q (a • z)=a • circularBoundedField νp νm η m q z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularBoundedField,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring

theorem circular_columns_coefficients_at_point (νp νm η : ℂ) (m : ℕ) (hm₀ : 1 ≤ m)
    (M : ℝ) (q : ℝ → ℂ) (Yp Ym : ℝ → E₄)
    (hq : ∀ t, 0 ≤ t → ‖q t‖ ≤ M)
    (hYp : ∀ t, 0 ≤ t → HasDerivAt Yp
      (circularLeadingField t (Yp t)+circularBoundedField νp νm η m (q t) (Yp t)) t)
    (hYm : ∀ t, 0 ≤ t → HasDerivAt Ym
      (circularLeadingField t (Ym t)+circularBoundedField νp νm η m (q t) (Ym t)) t)
    (hp : Filter.Tendsto Yp Filter.atTop (nhds ((1,0),(0,0))))
    (hm : Filter.Tendsto Ym Filter.atTop (nhds ((0,0),(1,0))))
    (a b : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : a • Yp r+b • Ym r=0) : a=0 ∧ b=0 := by
  let Z := fun t => a • Yp t+b • Ym t
  have hd : ∀ t, 0 ≤ t → HasDerivAt Z
      (circularLeadingField t (Z t)+circularBoundedField νp νm η m (q t) (Z t)) t := by
    intro t ht
    apply (((hYp t ht).const_smul a).add ((hYm t ht).const_smul b)).congr_deriv
    dsimp only [Z]
    rw [circularLeadingField_add,circularBoundedField_add,
      circularLeadingField_smul,circularLeadingField_smul,
      circularBoundedField_smul,circularBoundedField_smul]
    simp only [smul_add]
    abel
  apply circular_columns_coefficient_unique Yp Ym hp hm a b
  intro t ht
  change Z t=0
  rcases le_total r t with hrt | htr
  · exact circular_forward_zero νp νm η m hm₀ M 0 r q Z hq hd hr hz t hrt
  · exact circular_zero_of_zero_at νp νm η m hm₀ M 0 r q Z hq hd hz t ht htr

theorem circular_columns_at_linearIndependent (νp νm η : ℂ) (m : ℕ) (hm₀ : 1 ≤ m)
    (M : ℝ) (q : ℝ → ℂ) (Yp Ym : ℝ → E₄)
    (hq : ∀ t, 0 ≤ t → ‖q t‖ ≤ M)
    (hYp : ∀ t, 0 ≤ t → HasDerivAt Yp
      (circularLeadingField t (Yp t)+circularBoundedField νp νm η m (q t) (Yp t)) t)
    (hYm : ∀ t, 0 ≤ t → HasDerivAt Ym
      (circularLeadingField t (Ym t)+circularBoundedField νp νm η m (q t) (Ym t)) t)
    (hp : Filter.Tendsto Yp Filter.atTop (nhds ((1,0),(0,0))))
    (hm : Filter.Tendsto Ym Filter.atTop (nhds ((0,0),(1,0)))) (r : ℝ) (hr : 0 ≤ r) :
    LinearIndependent ℂ ![Yp r,Ym r] := by
  rw [linearIndependent_fin2]
  constructor
  · change Ym r ≠ 0
    intro hz
    have he := circular_columns_coefficients_at_point νp νm η m hm₀ M q Yp Ym hq hYp hYm hp hm
      0 1 r hr (by simp [hz])
    exact one_ne_zero he.2
  · intro a ha
    change a • Ym r=Yp r at ha
    have he := circular_columns_coefficients_at_point νp νm η m hm₀ M q Yp Ym hq hYp hYm hp hm
      (-1) a r hr (by rw [ha]; simp)
    exact (neg_ne_zero.mpr one_ne_zero) he.1

end DefocusingNLS

end OAI
