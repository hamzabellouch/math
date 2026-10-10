import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.ActualMeanComparison
import OAI.Analysis.CoulombIonization.Variational.PatchCenterIntegrable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace CoulombAnalysis

lemma field_lower_from_good_gap {W D H eta C e : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (heta : 0 < eta) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hg : D ≤ eta → H ≤ W) (hn : max (-W) 0 ≤ C*D+e) :
    H-(H/eta+C)*D-e ≤ W := by
  by_cases hd : D ≤ eta
  · have hh := hg hd
    have hb : 0 ≤ (H/eta+C)*D := mul_nonneg (add_nonneg (div_nonneg hH heta.le) hC) hD
    linarith
  · have hb : H ≤ (H/eta)*D := by
      calc
        H = (H/eta)*eta := (div_mul_cancel₀ H heta.ne').symm
        _ ≤ (H/eta)*D := mul_le_mul_of_nonneg_left (le_of_not_ge hd) (div_nonneg hH heta.le)
    have hn' := (le_max_left (-W) 0).trans hn
    nlinarith

lemma field_upper_from_good_gap {W D H eta C : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (heta : 0 < eta) (hC : 0 ≤ C)
    (hg : D ≤ eta → W ≤ H) (hc : W ≤ C) :
    W ≤ H+(C/eta)*D := by
  by_cases hd : D ≤ eta
  · have hh := hg hd
    have hb : 0 ≤ (C/eta)*D := mul_nonneg (div_nonneg hC heta.le) hD
    linarith
  · have hb : C ≤ (C/eta)*D := by
      calc
        C = (C/eta)*eta := (div_mul_cancel₀ C heta.ne').symm
        _ ≤ (C/eta)*D := mul_le_mul_of_nonneg_left (le_of_not_ge hd) (div_nonneg hC heta.le)
    linarith

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

theorem conditional_high_mean_expected_center {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta m : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2)
    (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hcount : ∀ᵐ u, m ≤ ∫ z in ball (0 : Space) q,
      retainedPatchLp hb (S u) u y R z ∂ballMeasure R)
    (hhigh : ∀ᵐ u,
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
        ∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R) :
    H*(∫ u, formMass (coreSlice ψ t u))-
      (H/eta+2/m)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u)-
      (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*(∫ u, formMass (coreSlice ψ t u)) ≤
      ∫ u, weightedPatchCenter ψ t Z lam y R u := by
  have hOsc := tfPatchOscillationConstant_pos
  have hbound : ∀ᵐ u,
      H*formMass (coreSlice ψ t u)-(H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u-
        (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*formMass (coreSlice ψ t u) ≤
      weightedPatchCenter ψ t Z lam y R u := by
    filter_upwards [hψ.ae_coreSlice t,hcount,hhigh] with u hu hcu hhu
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hn := conditionalPatchMinimizer_negative_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
      (retainedPatchLp_nonneg hb (S u) u y R) hq hqR hsmall hm hcu
    have hg : D ≤ eta → H ≤ conditionalPatchCenter ψ t Z lam y R u := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_high_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR (hsmall.trans (by norm_num)) hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt hhu
    have he := field_lower_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ 2/m)
      (by positivity : 0 ≤ 2*(tfPatchOscillationConstant/R*q)*R⁻¹^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hn)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hfirst : Integrable (fun u => H*formMass (coreSlice ψ t u)-
      (H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u) :=
    (hmassi.const_mul H).sub (hi.const_mul (H/eta+2/m))
  have hleft := hfirst.sub
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4))
  have he := integral_mono_ae hleft
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hbound
  simp only [Pi.sub_apply] at he
  rw [integral_sub hfirst
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)),
    integral_sub (hmassi.const_mul H) (hi.const_mul (H/eta+2/m)),
    integral_const_mul,integral_const_mul,integral_const_mul] at he
  exact he

theorem conditional_low_mean_expected_center {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hH : 0 ≤ H) (heta : 0 < eta)
    (hlow : ∀ᵐ u, (∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
      (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)) :
    (∫ u, weightedPatchCenter ψ t Z lam y R u) ≤
      H*(∫ u, formMass (coreSlice ψ t u))+
        ((tfPatchCapConstant/R^4)/eta)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u) := by
  have hCap := tfPatchCapConstant_pos
  have hbound : ∀ᵐ u,
      weightedPatchCenter ψ t Z lam y R u ≤
      H*formMass (coreSlice ψ t u)+((tfPatchCapConstant/R^4)/eta)*weightedPatchGap ψ t Z lam y R hb S u := by
    filter_upwards [hψ.ae_coreSlice t,hlow] with u hu hlu
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hc := conditionalPatchMinimizer_nonradial_cap ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam 0
      (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*R/4))
    have hg : D ≤ eta → conditionalPatchCenter ψ t Z lam y R u ≤ H := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_low_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt hlu
    have he := field_upper_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ tfPatchCapConstant/R^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hc)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hright := (hmassi.const_mul H).add (hi.const_mul ((tfPatchCapConstant/R^4)/eta))
  have he := integral_mono_ae
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hright hbound
  simp only [Pi.add_apply] at he
  rw [integral_add (hmassi.const_mul H) (hi.const_mul ((tfPatchCapConstant/R^4)/eta)),
    integral_const_mul,integral_const_mul] at he
  exact he

end CoulombAtom

end

end OAI
