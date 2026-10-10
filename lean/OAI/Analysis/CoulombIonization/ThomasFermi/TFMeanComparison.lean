import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.RadialPatchCap
import OAI.Analysis.CoulombIonization.Variational.NegativePatchControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom

lemma oscillation_upper_of_center_le {w v δ B H : ℝ} (hδ : δ ≤ 1)
    (hH : 0 ≤ H) (hv : v ≤ H) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    w ≤ H+δ*B := by
  have hh := (abs_le.mp ho).2
  by_cases h : 0 ≤ v
  · rw [max_eq_right (by linarith : -v ≤ 0)] at hh
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -v)] at hh
    have hp := mul_nonneg (sub_nonneg.mpr hδ) (neg_nonneg.mpr (le_of_not_ge h))
    nlinarith

lemma oscillation_lower_of_center_ge {w v δ B H : ℝ}
    (hH : 0 ≤ H) (hv : H ≤ v) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    H-δ*B ≤ w := by
  have hh := (abs_le.mp ho).1
  rw [max_eq_right (by linarith : -v ≤ 0)] at hh
  linarith

lemma tf_euler_density_mono {a u v : ℝ} (ha : 0 ≤ a) (huv : u ≤ v) :
    (max u 0/a)^(3/2:ℝ) ≤ (max v 0/a)^(3/2:ℝ) := by
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) ha) _ (by norm_num)
  exact div_le_div_of_nonneg_right (max_le_max huv le_rfl) ha

lemma tf_density_average_upper {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ W k : α → ℝ} {a v δ B H : ℝ}
    (ha : 0 ≤ a) (hδ : δ ≤ 1) (hH : 0 ≤ H) (hv : v ≤ H)
    (he : ∀ᵐ x ∂μ, ρ x = (max (W x) 0/a)^(3/2:ℝ))
    (hn : ∀ᵐ x ∂μ, 0 ≤ k x) (hi : Integrable k μ)
    (hp : Integrable (fun x => k x*ρ x) μ)
    (ho : ∀ᵐ x ∂μ, k x ≠ 0 → |W x-v| ≤ δ*(B+max (-v) 0)) :
    (∫ x, k x*ρ x ∂μ) ≤ (max (H+δ*B) 0/a)^(3/2:ℝ)*(∫ x, k x ∂μ) := by
  rw [←integral_const_mul]
  apply integral_mono_ae hp (hi.const_mul _)
  filter_upwards [he,hn,ho] with x hx hkn hox
  by_cases hk : k x = 0
  · simp only [hk,zero_mul,mul_zero,le_refl]
  · rw [hx,mul_comm (k x)]
    exact mul_le_mul_of_nonneg_right
      (tf_euler_density_mono ha (oscillation_upper_of_center_le hδ hH hv (hox hk))) hkn

lemma tf_density_average_lower {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ W k : α → ℝ} {a v δ B H : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hv : H ≤ v)
    (he : ∀ᵐ x ∂μ, ρ x = (max (W x) 0/a)^(3/2:ℝ))
    (hn : ∀ᵐ x ∂μ, 0 ≤ k x) (hi : Integrable k μ)
    (hp : Integrable (fun x => k x*ρ x) μ)
    (ho : ∀ᵐ x ∂μ, k x ≠ 0 → |W x-v| ≤ δ*(B+max (-v) 0)) :
    (max (H-δ*B) 0/a)^(3/2:ℝ)*(∫ x, k x ∂μ) ≤ (∫ x, k x*ρ x ∂μ) := by
  rw [←integral_const_mul]
  apply integral_mono_ae (hi.const_mul _) hp
  filter_upwards [he,hn,ho] with x hx hkn hox
  by_cases hk : k x = 0
  · simp only [hk,zero_mul,mul_zero,le_refl]
  · rw [hx,mul_comm (k x)]
    exact mul_le_mul_of_nonneg_right
      (tf_euler_density_mono ha (oscillation_lower_of_center_ge hH hv (hox hk))) hkn

theorem tfPatchMinimizer_mean_upper (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (W : Space → ℝ)
    (hW : ∀ᵐ x ∂ballMeasure R, W x = Φ x-tfBallPotential R (tfPatchMinimizer R T hT Φ) x)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {δ B H : ℝ}
    (hδ : δ ≤ 1) (hH : 0 ≤ H) (hv : W 0 ≤ H)
    (ho : ∀ᵐ x ∂ballMeasure R, k x ≠ 0 → |W x-W 0| ≤ δ*(B+max (-W 0) 0)) :
    (∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R) ≤
      (max (H+δ*B) 0/((5/3:ℝ)*T))^(3/2:ℝ)*(∫ x, k x ∂ballMeasure R) := by
  apply tf_density_average_upper (mul_nonneg (by norm_num) hT.le) hδ hH hv _ hkn
    (hk.integrable (Fact.out : (1:ENNReal) ≤ 5/2)) (hk.integrable_mul (Lp.memLp _)) ho
  have he := tfPatchFunctional_euler R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hW] with x hx hWx
  rw [hx,hWx]

theorem tfPatchMinimizer_mean_lower (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (W : Space → ℝ)
    (hW : ∀ᵐ x ∂ballMeasure R, W x = Φ x-tfBallPotential R (tfPatchMinimizer R T hT Φ) x)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {δ B H : ℝ}
    (hH : 0 ≤ H) (hv : H ≤ W 0)
    (ho : ∀ᵐ x ∂ballMeasure R, k x ≠ 0 → |W x-W 0| ≤ δ*(B+max (-W 0) 0)) :
    (max (H-δ*B) 0/((5/3:ℝ)*T))^(3/2:ℝ)*(∫ x, k x ∂ballMeasure R) ≤
      ∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R := by
  apply tf_density_average_lower (mul_nonneg (by norm_num) hT.le) hH hv _ hkn
    (hk.integrable (Fact.out : (1:ENNReal) ≤ 5/2)) (hk.integrable_mul (Lp.memLp _)) ho
  have he := tfPatchFunctional_euler R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hW] with x hx hWx
  rw [hx,hWx]

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

theorem conditionalPatchMinimizer_negative_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {q m : ℝ} (hq : 0 < q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2) (hm : 0 < m)
    (hcount : m ≤ ∫ z in ball (0 : Space) q, σ z ∂ballMeasure R) :
    let Φ := conditionalPatchField ψ t Z lam y R u
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
    max (-W 0) 0 ≤ (2/m)*tfPatchGap R tfKinetic tfKinetic_pos Φ σ+
      2*(tfPatchOscillationConstant/R*q)*R⁻¹^4 := by
  dsimp only
  refine tfPatchGap_negative_center_control R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u) hσ
    (fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-
      tfBallPotential R (tfPatchMinimizer R tfKinetic tfKinetic_pos
        (conditionalPatchField ψ t Z lam y R u)) z)
    (B := R⁻¹^4) ?_ hsmall hm hcount ?_
  · have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    have he := conditionalPatchField_ae ψ t Z lam y R u hp
    filter_upwards [he] with z hz
    rw [hz]
  · intro z hz
    have hzq : ‖z‖ ≤ q := (mem_ball_zero_iff.mp hz).le
    have hRlarge : 0 < R/12 := hq.trans_le hqR
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

theorem conditionalRetained_negative_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    {q m : ℝ} (hq : 0 < q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2) (hm : 0 < m)
    (hcount : m ≤ ∫ z in ball (0 : Space) q, retainedPatchLp hb (S u) u y R z ∂ballMeasure R) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
    formMass (coreSlice ψ t u)*max (-W 0) 0 ≤
      (2/m)*weightedPatchGap ψ t Z lam y R hb S u+
        (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*formMass (coreSlice ψ t u) := by
  have hh := conditionalPatchMinimizer_negative_center ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
    (retainedPatchLp_nonneg hb (S u) u y R) hq hqR hsmall hm hcount
  have he := mul_le_mul_of_nonneg_left hh (formMass_nonneg (coreSlice ψ t u))
  dsimp only at he ⊢
  apply he.trans_eq
  dsimp [weightedPatchGap]
  ring

end CoulombAtom

end

end OAI
