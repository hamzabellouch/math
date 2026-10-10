import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PatchCenterObservable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchGap_lipschitz_abs_difference {R q : ℝ} (hq : 0 < q) (hqR : 2*q < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R) {σ : TFLp (ballMeasure R)}
    (hσ : NonnegDensity σ) {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k)
    (hs : Function.support k ⊆ closedBall 0 q) :
    |(∫ x, k x*σ x ∂ballMeasure R)-(∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R)| ≤
      Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R T hT Φ σ) := by
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := Real.abs_le_sqrt (tfPatchGap_lipschitz_control hq hqR T hT Φ hσ hk hs)
  have hpair : (∫ x, k x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R) =
      (∫ x, k x*σ x ∂ballMeasure R)-(∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R) := by
    have h1 : Integrable (fun x => k x*σ x) (ballMeasure R) :=
      hm.integrable_mul (Lp.memLp σ)
    have h2 : Integrable (fun x => k x*tfPatchMinimizer R T hT Φ x) (ballMeasure R) :=
      hm.integrable_mul (Lp.memLp _)
    rw [←integral_sub h1 h2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub σ (tfPatchMinimizer R T hT Φ)] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  rw [hpair] at he
  exact he

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma conditionalPatchMinimizer_mean_upper {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {q H : ℝ}
    (hs : ∀ z, k z ≠ 0 → ‖z‖ ≤ q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1) (hH : 0 ≤ H)
    (hv : conditionalPatchCenter ψ t Z lam y R u ≤ H) :
    (∫ x, k x*tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) x ∂ballMeasure R) ≤
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
  have hW : ∀ᵐ z ∂ballMeasure R, W z = conditionalPatchField ψ t Z lam y R u z-tfBallPotential R f z := by
    have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hp] with z hz
    simp only [W,hz]
  apply tfPatchMinimizer_mean_upper R tfKinetic tfKinetic_pos _ W hW hk hkn hsmall hH
    (by simpa only [W,conditionalPatchCenter,add_zero] using hv)
  exact Eventually.of_forall fun z hz => by
    have hzq := hs z hz
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

lemma conditionalPatchMinimizer_mean_lower {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {q H : ℝ}
    (hs : ∀ z, k z ≠ 0 → ‖z‖ ≤ q) (hqR : q ≤ R/12) (hH : 0 ≤ H)
    (hv : H ≤ conditionalPatchCenter ψ t Z lam y R u) :
    (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R) ≤
      ∫ x, k x*tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) x ∂ballMeasure R := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
  have hW : ∀ᵐ z ∂ballMeasure R, W z = conditionalPatchField ψ t Z lam y R u z-tfBallPotential R f z := by
    have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hp] with z hz
    simp only [W,hz]
  apply tfPatchMinimizer_mean_lower R tfKinetic tfKinetic_pos _ W hW hk hkn hH
    (by simpa only [W,conditionalPatchCenter,add_zero] using hv)
  exact Eventually.of_forall fun z hz => by
    have hzq := hs z hz
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

theorem conditionalPatch_high_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1) (hH : 0 ≤ H)
    (hhigh :
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) σ) <
        ∫ x, k x*σ x ∂ballMeasure R) :
    H < conditionalPatchCenter ψ t Z lam y R u := by
  by_contra hv
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := conditionalPatchMinimizer_mean_upper ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
    hm (Eventually.of_forall hkn) (fun z hz => mem_closedBall_zero_iff.mp (hs hz)) hqR hsmall hH (le_of_not_gt hv)
  have hc := (abs_le.mp (tfPatchGap_lipschitz_abs_difference hq (by linarith : 2*q < R)
    tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) hσ hk hs)).2
  linarith

theorem conditionalPatch_low_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q) (hqR : q ≤ R/12) (hH : 0 ≤ H)
    (hlow : (∫ x, k x*σ x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) σ) <
      (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)) :
    conditionalPatchCenter ψ t Z lam y R u < H := by
  by_contra hv
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := conditionalPatchMinimizer_mean_lower ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
    hm (Eventually.of_forall hkn) (fun z hz => mem_closedBall_zero_iff.mp (hs hz)) hqR hH (le_of_not_gt hv)
  have hc := (abs_le.mp (tfPatchGap_lipschitz_abs_difference hq (by linarith : 2*q < R)
    tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) hσ hk hs)).1
  linarith

end CoulombAtom

end

end OAI
