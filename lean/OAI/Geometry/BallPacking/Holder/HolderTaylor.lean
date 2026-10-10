import Mathlib
import OAI.Geometry.BallPacking.Holder.SchauderSplit

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped Topology
open Set Filter
open scoped ContDiff
open MeasureTheory
section
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
 [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_taylor_remainder {f : D → E} (hf : Differentiable ℝ f)
    {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hdf : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ M*‖x-y‖^α) (x h : D) :
    ‖f (x+h)-f x-fderiv ℝ f x h‖ ≤ (M*‖h‖^α)*‖h‖ := by
  have hball : x+h ∈ Metric.closedBall x ‖h‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl]
  have hb (z : D) (hz : z ∈ Metric.closedBall x ‖h‖) :
      ‖fderiv ℝ f z-fderiv ℝ f x‖ ≤ M*‖h‖^α := by
    apply (hdf z x).trans
    apply mul_le_mul_of_nonneg_left _ hM
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have he := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) hb
    (Metric.mem_closedBall_self (norm_nonneg h)) hball
  simpa only [add_sub_cancel_left] using he

lemma hasFDerivAt_of_holder_remainder {f : D → E} (L : D →L[ℝ] E) (x : D)
    {C α : ℝ} (hα : 0 < α)
    (hb : ∀ h, ‖f (x+h)-f x-L h‖ ≤ (C*‖h‖^α)*‖h‖) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have ht : Tendsto (fun h : D => C*‖h‖^α) (𝓝 0) (𝓝 (0:ℝ)) := by
    simpa only [norm_zero, Real.zero_rpow hα.ne', mul_zero] using
      (show Tendsto (fun h : D => C*‖h‖^α) (𝓝 0) (𝓝 (C*‖(0:D)‖^α)) from
        (continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr hα.le))).tendsto 0)
  filter_upwards [(tendsto_order.mp ht).2 c hc] with h hh
  exact (hb h).trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
lemma holder_continuous {f : D → E} {C α : ℝ} (hα : 0 < α)
    (hb : ∀ x y, ‖f x-f y‖ ≤ C*‖x-y‖^α) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun y : D => C*‖y-x‖^α) (𝓝 x) (𝓝 (0:ℝ)) := by
    have hcont : Continuous (fun y : D => C*‖y-x‖^α) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        (fun _ => Or.inr hα.le))
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hcont.tendsto x
  exact squeeze_zero (fun _ => norm_nonneg _) (fun y => hb y x) ht

lemma hasFDerivAt_limit_of_holder_derivative {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → D → E} {L : ι → D → (D →L[ℝ] E)} {f₀ : D → E} {L₀ : D → D →L[ℝ] E}
    {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hd : ∀ᶠ i in l, ∀ x, HasFDerivAt (f i) (L i x) x)
    (hH : ∀ᶠ i in l, ∀ x y, ‖L i x-L i y‖ ≤ M*‖x-y‖^α)
    (hf : ∀ x, Tendsto (fun i => f i x) l (𝓝 (f₀ x)))
    (hL : ∀ x, Tendsto (fun i => L i x) l (𝓝 (L₀ x))) (x : D) :
    HasFDerivAt f₀ (L₀ x) x := by
  apply hasFDerivAt_of_holder_remainder _ x hα
  intro v
  have htL := (ContinuousLinearMap.apply ℝ E v).continuous.tendsto (L₀ x) |>.comp (hL x)
  apply le_of_tendsto (((hf (x+v)).sub (hf x)).sub htL).norm
  filter_upwards [hd, hH] with i hi hh
  have hEq : fderiv ℝ (f i) = L i := funext fun z => (hi z).fderiv
  have he := holder_taylor_remainder (fun z => (hi z).differentiableAt) hM hα.le
    (fun z w => by rw [hEq]; exact hh z w) x v
  change ‖f i (x+v)-f i x-L i x v‖ ≤ _
  simpa only [hEq] using he

end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma cutoffCauchyDerivative_holder (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ x y : ℂ,
      ‖cutoffCauchyDerivative b g x-cutoffCauchyDerivative b g y‖ ≤ C*H*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨C,hC,h⟩ := cutoff_smoothCauchyKernel_full_schauder (E := E) b
  refine ⟨C,hC,?_⟩
  intro g hgC H hH hg x y
  apply le_of_tendsto (((cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x).sub
    (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg y)).norm)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact h g hgC H hH hg δ hδ x y

lemma cutoffCauchy_hasFDerivAt (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume)
      (cutoffCauchyDerivative b g x) x := by
  obtain ⟨C,hC,h⟩ := cutoff_smoothCauchyKernel_full_schauder (E := E) b
  apply hasFDerivAt_of_holder_remainder (C := C*H) (α := (1:ℝ)/3) _ x (by norm_num)
  intro v
  have hd := (ContinuousLinearMap.apply ℝ E v).continuous.tendsto (cutoffCauchyDerivative b g x)
    |>.comp (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x)
  have ht := (((cutoff_smoothCauchyKernel_convolution_tendsto b hgC (x+v)).sub
    (cutoff_smoothCauchyKernel_convolution_tendsto b hgC x)).sub hd).norm
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hK : ContDiff ℝ ∞ (fun w => b w • smoothCauchyKernel δ w) :=
    b.contDiff.smul (smoothCauchyKernel_smooth hδ)
  have hcK : HasCompactSupport (fun w => b w • smoothCauchyKernel δ w) :=
    b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)
  have hf : Differentiable ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g (ContinuousLinearMap.lsmul ℝ ℂ) volume) :=
    fun z => (hcK.hasFDerivAt_convolution_left _ (hK.of_le (by simp)) hgC.locallyIntegrable z).differentiableAt
  exact holder_taylor_remainder hf (mul_nonneg hC hH) (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    (h g hgC H hH hg δ hδ) x v

lemma cutoffCauchy_contDiff_one (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (cutoffCauchy_hasFDerivAt b hgC hH hg x).differentiableAt, ?_⟩
  have he : fderiv ℝ (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume) =
      cutoffCauchyDerivative b g := funext fun x => (cutoffCauchy_hasFDerivAt b hgC hH hg x).fderiv
  rw [he]
  obtain ⟨C,hC,h⟩ := cutoffCauchyDerivative_holder (E := E) b
  exact holder_continuous (by norm_num : (0:ℝ) < (1:ℝ)/3) (h g hgC H hH hg)

lemma cutoffCauchy_fderiv_bound (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ x : ℂ,
      ‖cutoffCauchyDerivative b g x‖ ≤ C*H := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let L : ℝ := (C+3)*(∫ w : ℂ, cauchySchauderWeight b.rOut w)
  have hw0 (w : ℂ) : 0 ≤ cauchySchauderWeight b.rOut w := by
    apply indicator_nonneg _ w
    intro z _
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hL : 0 ≤ L := mul_nonneg (by linarith) (integral_nonneg hw0)
  refine ⟨L,hL,?_⟩
  intro g hgC H hH hg x
  apply le_of_tendsto (cutoff_smoothCauchyKernel_derivative_tendsto b hgC hH hg x).norm
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have he := compact_kernel_convolution_derivative_bound
    (K := fun w => b w • smoothCauchyKernel δ w)
    (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
    (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) hgC
    ((cauchySchauderWeight_integrable b.rOut).const_mul ((C+3)*H))
    (cutoff_smoothCauchyKernel_schauder_bound b hC hCb hH hg hδ) x
  apply he.trans_eq
  rw [integral_const_mul]
  dsimp only [L]
  ring

end
section

local instance : NormedAddCommGroup (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace

def tailCauchyKernel (δ : ℝ) (z : ℂ) : ℂ :=
  (1 - scaledSchauderBump 1 z) • smoothCauchyKernel δ z

def tailCauchyJet (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (1-scaledSchauderBump 1 z) • regularizedCauchyJet δ z -
    (fderiv ℝ (scaledSchauderBump 1) z).smulRight (smoothCauchyKernel δ z)

lemma tailCauchyKernel_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (tailCauchyKernel δ) :=
  (contDiff_const.sub (scaledSchauderBump_smooth 1)).smul (smoothCauchyKernel_smooth hδ)

lemma tailCauchyKernel_eventually_zero (δ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    tailCauchyKernel δ =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [scaledSchauderBump_eventually_one (by norm_num : (0:ℝ) < 1) hz] with w hw
  simp only [tailCauchyKernel, hw, sub_self, zero_smul]

lemma tailCauchyJet_eq {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (tailCauchyKernel δ) z = tailCauchyJet δ z := by
  change fderiv ℝ (fun w => (1-scaledSchauderBump 1 w) • smoothCauchyKernel δ w) z = _
  rw [fderiv_fun_smul
    ((contDiff_const.sub (scaledSchauderBump_smooth 1)).differentiable (by simp) z)
    ((smoothCauchyKernel_smooth hδ).differentiable (by simp) z),
    regularizedCauchyJet_eq hδ, fderiv_const_sub]
  ext v
  simp only [tailCauchyJet, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, neg_smul, sub_eq_add_neg]

lemma tailCauchyKernel_zero (z : ℂ) : tailCauchyKernel 0 z = (1-schauderBump z) • z⁻¹ := by
  have he : (‖z‖^2)⁻¹ • star z = z⁻¹ := by
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    exact mul_comm _ _
  simpa only [tailCauchyKernel, scaledSchauderBump, smoothCauchyKernel,
    inv_one, one_smul, add_zero] using congrArg ((1-schauderBump z) • ·) he

lemma tailCauchyKernel_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => tailCauchyKernel δ z) (𝓝[>] 0) (𝓝 (tailCauchyKernel 0 z)) := by
  rw [tailCauchyKernel_zero]
  simpa only [tailCauchyKernel, scaledSchauderBump, inv_one, one_smul] using
    (tendsto_const_nhds.smul (smoothCauchyKernel_tendsto z) :
      Tendsto (fun δ : ℝ => (1-schauderBump z) • smoothCauchyKernel δ z) _ _)

lemma tailCauchyJet_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => tailCauchyJet δ z) (𝓝[>] 0) (𝓝 (tailCauchyJet 0 z)) := by
  by_cases hz : z = 0
  · subst z
    have he := scaledSchauderBump_eventually_one (by norm_num : (0:ℝ) < 1)
      (by simp : ‖(0:ℂ)‖ ≤ (1:ℝ))
    have hd : fderiv ℝ (scaledSchauderBump 1) 0 = 0 := he.fderiv_eq.trans (by simp)
    simp only [tailCauchyJet, he.eq_of_nhds, sub_self, zero_smul, hd,
      ContinuousLinearMap.zero_smulRight]
    exact tendsto_const_nhds
  · have hv : ContinuousAt (fun δ : ℝ => smoothCauchyKernel δ z) 0 := by
      have hn : ‖z‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
      have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
        (continuousAt_const.add continuousAt_id).inv₀ (by simpa using hn)
      exact hi.smul (show ContinuousAt (fun _ : ℝ => star z) 0 from continuousAt_const)
    have hA : ContinuousAt (fun δ : ℝ => (1-scaledSchauderBump 1 z) • regularizedCauchyJet δ z) 0 :=
      (show ContinuousAt (fun _ : ℝ => 1-scaledSchauderBump 1 z) 0 from continuousAt_const).smul
        (regularizedCauchyJet_continuousAt hz)
    have hB : ContinuousAt (fun δ : ℝ => (fderiv ℝ (scaledSchauderBump 1) z).smulRight
        (smoothCauchyKernel δ z)) 0 :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ (fderiv ℝ (scaledSchauderBump 1) z)).continuous.continuousAt.comp hv
    have ht : ContinuousAt (fun δ : ℝ => tailCauchyJet δ z) 0 := hA.sub hB
    exact ht.tendsto.mono_left nhdsWithin_le_nhds

lemma tailCauchyKernel_uniform_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∀ z : ℂ,
      ‖tailCauchyKernel δ z‖ ≤ 1 ∧ ‖fderiv ℝ (tailCauchyKernel δ) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ 2 (tailCauchyKernel δ) z‖ ≤ B := by
  obtain ⟨M,hM,hjet⟩ := scaledSchauderBump_homogeneous_bounds
  refine ⟨3+2*M,14+4*M*3+4*M,by positivity,by positivity,?_⟩
  intro δ hδ z
  by_cases hz : ‖z‖ ≤ 1
  · have he := tailCauchyKernel_eventually_zero δ hz
    have hd : fderiv ℝ (tailCauchyKernel δ) z = 0 := he.fderiv_eq.trans (by simp)
    have hd2 : iteratedFDeriv ℝ 2 (tailCauchyKernel δ) z = 0 :=
      (he.iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds.trans (by simp)
    simp only [he.eq_of_nhds, hd, hd2, norm_zero]
    exact ⟨zero_le_one, by positivity, by positivity⟩
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hb := scaledSchauderBump_range 1 z
    have hbn : ‖1-scaledSchauderBump 1 z‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr hb.2)]
      linarith [hb.1]
    have h0 := smoothCauchyKernel_norm hδ z
    have h1 := smoothCauchyKernel_first_opNorm hδ hz0
    have h2 := smoothCauchyKernel_second_opNorm hδ hz0
    have hj := hjet 1 (by norm_num) z hz0
    refine ⟨?_,?_,?_⟩
    · calc
        _ ≤ 1*‖z‖⁻¹ := by
          rw [tailCauchyKernel, norm_smul]
          exact mul_le_mul hbn h0 (norm_nonneg _) zero_le_one
        _ ≤ 1 := by rw [one_mul]; exact inv_le_one_of_one_le₀ hz1.le
    · have hd := first_near_bound (smoothCauchyKernel_smooth hδ)
        (contDiff_const.sub (scaledSchauderBump_smooth 1)) hM (by norm_num : (0:ℝ) ≤ 3)
        hz0 hbn (by rw [fderiv_const_sub, norm_neg]; exact hj.1) h0 h1
      exact hd.trans (div_le_self (by positivity) (one_le_pow₀ hz1.le))
    · have hd := second_far_bound (smoothCauchyKernel_smooth hδ) (scaledSchauderBump_smooth 1)
        hM (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) ≤ 14)
        hz0 hbn hj.1 hj.2 h0 h1 h2
      exact hd.trans (div_le_self (by positivity) (one_le_pow₀ hz1.le))

lemma tailCauchyKernel_hasFDerivAt (z : ℂ) :
    HasFDerivAt (tailCauchyKernel 0) (tailCauchyJet 0 z) z := by
  obtain ⟨A,B,hA,hB,hjet⟩ := tailCauchyKernel_uniform_bounds
  apply hasFDerivAt_limit_of_holder_derivative (M := B) (α := 1) hB (by norm_num)
    (l := 𝓝[>] (0:ℝ)) (f := tailCauchyKernel) (L := tailCauchyJet)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro w
    rw [← tailCauchyJet_eq hδ]
    exact ((tailCauchyKernel_smooth hδ).differentiable (by simp) w).hasFDerivAt
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro w t
    simp_rw [← tailCauchyJet_eq hδ]
    rw [Real.rpow_one]
    apply HolderCompletion.norm_sub_le_of_deriv_bound
      (((tailCauchyKernel_smooth hδ).fderiv_right (m := ∞) (by simp)).differentiable (by simp))
    intro u
    rw [← norm_second_jet]
    exact (hjet δ hδ u).2.2
  · exact tailCauchyKernel_tendsto
  · exact tailCauchyJet_tendsto

lemma tailCauchyKernel_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ z : ℂ, ‖tailCauchyKernel 0 z‖ ≤ 1 ∧ ‖tailCauchyJet 0 z‖ ≤ A) ∧
      (∀ z w : ℂ, ‖tailCauchyJet 0 z-tailCauchyJet 0 w‖ ≤ B*‖z-w‖) := by
  obtain ⟨A,B,hA,hB,hjet⟩ := tailCauchyKernel_uniform_bounds
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro z
    constructor
    · apply le_of_tendsto (tailCauchyKernel_tendsto z).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hjet δ hδ z).1
    · apply le_of_tendsto (tailCauchyJet_tendsto z).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [← tailCauchyJet_eq hδ]
      exact (hjet δ hδ z).2.1
  · intro z w
    apply le_of_tendsto ((tailCauchyJet_tendsto z).sub (tailCauchyJet_tendsto w)).norm
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp_rw [← tailCauchyJet_eq hδ]
    apply HolderCompletion.norm_sub_le_of_deriv_bound
      (((tailCauchyKernel_smooth hδ).fderiv_right (m := ∞) (by simp)).differentiable (by simp))
    intro u
    rw [← norm_second_jet]
    exact (hjet δ hδ u).2.2

lemma tailCauchyKernel_contDiff_one : ContDiff ℝ 1 (tailCauchyKernel 0) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (tailCauchyKernel_hasFDerivAt z).differentiableAt,?_⟩
  have he : fderiv ℝ (tailCauchyKernel 0) = tailCauchyJet 0 :=
    funext fun z => (tailCauchyKernel_hasFDerivAt z).fderiv
  rw [he]
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact holder_continuous (α := 1) (by norm_num) (by simpa only [Real.rpow_one] using hL)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def tailCauchyTransform (g : ℂ → E) : ℂ → E :=
  convolution (tailCauchyKernel 0) g (ContinuousLinearMap.lsmul ℝ ℂ) volume

def tailIntegralJet (g : ℂ → E) (x w : ℂ) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g w)).comp (tailCauchyJet 0 (x-w))

def tailCauchyDerivative (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∫ w : ℂ, tailIntegralJet g x w

omit [CompleteSpace E] in
lemma tailCauchyTransform_eq (g : ℂ → E) (x : ℂ) :
    tailCauchyTransform g x = ∫ w : ℂ, tailCauchyKernel 0 (x-w) • g w :=
  convolution_eq_swap _

lemma tailCauchyJet_continuous : Continuous (tailCauchyJet 0) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact holder_continuous (α := 1) (by norm_num) (by simpa only [Real.rpow_one] using hL)

omit [CompleteSpace E] in
lemma tailIntegralJet_continuous {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Continuous (tailIntegralJet g x) :=
  (((ContinuousLinearMap.lsmul ℝ ℂ).flip).continuous.comp hg).clm_comp
    (tailCauchyJet_continuous.comp (continuous_const.sub continuous_id))

omit [CompleteSpace E] in
lemma tailIntegralJet_bound {A : ℝ} (hA : 0 ≤ A) (hJ : ∀ z, ‖tailCauchyJet 0 z‖ ≤ A)
    (g : ℂ → E) (x w : ℂ) : ‖tailIntegralJet g x w‖ ≤ A*‖g w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA (norm_nonneg _))
  intro v
  change ‖tailCauchyJet 0 (x-w) v • g w‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ (A*‖v‖)*‖g w‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hJ _) (norm_nonneg _)))
      (norm_nonneg _)
    _ = _ := by ring

omit [CompleteSpace E] in
lemma tailCauchy_hasFDerivAt {g : ℂ → E} (hg : Continuous g) (hi : Integrable g) (x : ℂ) :
    HasFDerivAt (tailCauchyTransform g) (tailCauchyDerivative g x) x := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  have hc : Continuous (tailCauchyKernel 0) := tailCauchyKernel_contDiff_one.continuous
  have hm (z : ℂ) : Continuous (fun w => tailCauchyKernel 0 (z-w) • g w) :=
    (hc.comp (continuous_const.sub continuous_id)).smul hg
  have ht (z : ℂ) : Integrable (fun w => tailCauchyKernel 0 (z-w) • g w) :=
    hi.norm.mono' (hm z).aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _))
  have he : tailCauchyTransform g = fun z => ∫ w : ℂ, tailCauchyKernel 0 (z-w) • g w :=
    funext (tailCauchyTransform_eq g)
  rw [he]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun w => A*‖g w‖)
    (F' := tailIntegralJet g) (univ_mem) (Eventually.of_forall fun z => (hm z).aestronglyMeasurable)
    (ht x) (tailIntegralJet_continuous hg x).aestronglyMeasurable
  · exact Eventually.of_forall fun w z _ => tailIntegralJet_bound hA (fun z => (hjet z).2) g z w
  · exact hi.norm.const_mul A
  · apply Eventually.of_forall
    intro w z _
    have hd := (tailCauchyKernel_hasFDerivAt (z-w)).comp z ((hasFDerivAt_id z).sub_const w)
    have hh := ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g w)).hasFDerivAt.comp z hd
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, tailIntegralJet] using hh

omit [CompleteSpace E] in
lemma tailCauchy_value_bound {g : ℂ → E} (hi : Integrable g) (x : ℂ) :
    ‖tailCauchyTransform g x‖ ≤ ∫ w : ℂ, ‖g w‖ := by
  rw [tailCauchyTransform_eq]
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  apply norm_integral_le_of_norm_le hi.norm
  exact Eventually.of_forall fun w => by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _)

omit [CompleteSpace E] in
lemma tailCauchy_derivative_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ g : ℂ → E, Continuous g → Integrable g →
      (∀ x, ‖tailCauchyDerivative g x‖ ≤ A*(∫ w : ℂ, ‖g w‖)) ∧
      (∀ x y, ‖tailCauchyDerivative g x-tailCauchyDerivative g y‖ ≤
        (B*(∫ w : ℂ, ‖g w‖))*‖x-y‖) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  refine ⟨A,B,hA,hB,?_⟩
  intro g hg hi
  have hj (x : ℂ) : Integrable (tailIntegralJet g x) :=
    (hi.norm.const_mul A).mono' (tailIntegralJet_continuous hg x).aestronglyMeasurable
      (Eventually.of_forall (tailIntegralJet_bound hA (fun z => (hjet z).2) g x))
  constructor
  · intro x
    exact (norm_integral_le_of_norm_le (hi.norm.const_mul A)
      (Eventually.of_forall (tailIntegralJet_bound hA (fun z => (hjet z).2) g x))).trans_eq
      (integral_const_mul A _)
  · intro x y
    rw [tailCauchyDerivative, tailCauchyDerivative, ← integral_sub (hj x) (hj y)]
    calc
      _ ≤ ∫ w : ℂ, (B*‖x-y‖)*‖g w‖ := by
        apply norm_integral_le_of_norm_le (hi.norm.const_mul (B*‖x-y‖))
        apply Eventually.of_forall
        intro w
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        change ‖tailCauchyJet 0 (x-w) v • g w-tailCauchyJet 0 (y-w) v • g w‖ ≤ _
        rw [← sub_smul, ← sub_apply, norm_smul]
        calc
          _ ≤ (‖tailCauchyJet 0 (x-w)-tailCauchyJet 0 (y-w)‖*‖v‖)*‖g w‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          _ ≤ ((B*‖x-y‖)*‖v‖)*‖g w‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            simpa only [sub_sub_sub_cancel_right] using hL (x-w) (y-w)
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; ring

lemma cutoffCauchyKernel_integrable (b : ContDiffBump (0:ℂ)) :
    Integrable (fun w : ℂ => b w • w⁻¹) :=
  locallyIntegrable_complex_inv.integrable_smul_left_of_hasCompactSupport b.continuous b.hasCompactSupport

omit [CompleteSpace E] in
lemma cutoffCauchy_convolution_integrable (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) (x : ℂ) : Integrable (fun w : ℂ => (b w • w⁻¹) • g (x-w)) := by
  have h := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
    (b.continuous.smul (hg.comp (continuous_const.sub continuous_id)))
    (b.hasCompactSupport.smul_right (f' := fun w => g (x-w)))
  have he : (fun w : ℂ => (b w • w⁻¹) • g (x-w)) =
      (fun w : ℂ => w⁻¹ • (b w • g (x-w))) := by
    funext w
    rw [smul_assoc, smul_comm (b w) (w⁻¹)]
  rw [he]
  exact h

omit [CompleteSpace E] in
lemma cutoffCauchy_value_bound (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x‖ ≤
      (∫ w : ℂ, ‖b w • w⁻¹‖)*M := by
  apply (norm_integral_le_of_norm_le ((cutoffCauchyKernel_integrable b).norm.mul_const M) ?_).trans_eq
    (integral_mul_const M _)
  apply Eventually.of_forall
  intro w
  change ‖(b w • w⁻¹) • g (x-w)‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

omit [CompleteSpace E] in
lemma cauchy_kernel_convolution_split {g : ℂ → E} (hg : Continuous g) (hi : Integrable g) :
    convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume =
      (fun x => convolution (fun w => schauderBump w • w⁻¹) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume x + tailCauchyTransform g x) := by
  funext x
  have htail : Integrable (fun w : ℂ => tailCauchyKernel 0 w • g (x-w)) := by
    have hc : Continuous (fun w => tailCauchyKernel 0 (x-w) • g w) :=
      (tailCauchyKernel_contDiff_one.continuous.comp (continuous_const.sub continuous_id)).smul hg
    obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
    have hh : Integrable (fun w : ℂ => tailCauchyKernel 0 (x-w) • g w) :=
      hi.norm.mono' hc.aestronglyMeasurable (Eventually.of_forall fun w => by
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_right (hjet _).1 (norm_nonneg _)).trans_eq (one_mul _))
    simpa only [sub_sub_self] using hh.comp_sub_left x
  have he (w : ℂ) : w⁻¹ = (schauderBump w • w⁻¹) + tailCauchyKernel 0 w := by
    rw [tailCauchyKernel_zero, ← add_smul]; simp
  change (∫ w : ℂ, w⁻¹ • g (x-w)) =
    (∫ w : ℂ, (schauderBump w • w⁻¹) • g (x-w)) +
    (∫ w : ℂ, tailCauchyKernel 0 w • g (x-w))
  rw [← integral_add (cutoffCauchy_convolution_integrable schauderBump hg x) htail]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by dsimp only; rw [← add_smul, ← he]

def globalCauchyDerivative (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  (Real.pi : ℂ)⁻¹ • (cutoffCauchyDerivative schauderBump g x + tailCauchyDerivative g x)

lemma cauchyTransform_holder_hasFDerivAt {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {H : ℝ} (hH : 0 ≤ H) (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (cauchyTransform g) (globalCauchyDerivative g x) x := by
  unfold cauchyTransform
  rw [cauchy_kernel_convolution_split hgC hi]
  exact ((cutoffCauchy_hasFDerivAt schauderBump hgC hH hg x).add
    (tailCauchy_hasFDerivAt hgC hi x)).const_smul _

lemma cauchyTransform_schauder_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → Integrable g →
      ∀ M H : ℝ, 0 ≤ M → 0 ≤ H → (∀ x, ‖g x‖ ≤ M) →
        (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) →
      (∀ x, ‖cauchyTransform g x‖ ≤ C*(M+H+∫ w : ℂ, ‖g w‖)) ∧
      (∀ x, ‖globalCauchyDerivative g x‖ ≤ C*(M+H+∫ w : ℂ, ‖g w‖)) ∧
      (∀ x y, ‖globalCauchyDerivative g x-globalCauchyDerivative g y‖ ≤
        C*(M+H+∫ w : ℂ, ‖g w‖)*‖x-y‖^((1:ℝ)/3)) := by
  obtain ⟨D,hD,hDb⟩ := cutoffCauchy_fderiv_bound (E := E) schauderBump
  obtain ⟨F,hF,hFb⟩ := cutoffCauchyDerivative_holder (E := E) schauderBump
  obtain ⟨A,B,hA,hB,hTb⟩ := tailCauchy_derivative_bounds (E := E)
  let K : ℝ := ∫ w : ℂ, ‖schauderBump w • w⁻¹‖
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  let c : ℝ := ‖(Real.pi : ℂ)⁻¹‖
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨c*(K+D+F+2*A+B+1),by positivity,?_⟩
  intro g hgC hi M H hM hH hb hh
  let I : ℝ := ∫ w : ℂ, ‖g w‖
  have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
  have htotal : 0 ≤ M+H+I := by positivity
  have hMI : M ≤ M+H+I := by linarith
  have hHI : H ≤ M+H+I := by linarith
  have hII : I ≤ M+H+I := by linarith
  have hDb' (x : ℂ) : ‖cutoffCauchyDerivative schauderBump g x‖ ≤ D*H := hDb g hgC H hH hh x
  have hTb' := hTb g hgC hi
  have hTh : ∀ x y, ‖tailCauchyDerivative g x-tailCauchyDerivative g y‖ ≤
      ((2*A+B)*I)*‖x-y‖^((1:ℝ)/3) := by
    have he := thirdHolderOn_of_bounded_lipschitz (s := (univ : Set ℂ))
      (mul_nonneg hA hI) (mul_nonneg hB hI) (fun x _ => hTb'.1 x)
      (fun x _ y _ => hTb'.2 x y)
    intro x y
    convert! he x (mem_univ x) y (mem_univ y) using 1; ring
  refine ⟨?_,?_,?_⟩
  · intro x
    change ‖(Real.pi : ℂ)⁻¹ •
      (convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x : E)‖ ≤ _
    rw [norm_smul, cauchy_kernel_convolution_split hgC hi]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (cutoffCauchy_value_bound schauderBump hb x) (tailCauchy_value_bound hi x))) hc).trans
    dsimp only [K, c, I] at *
    nlinarith [mul_le_mul_of_nonneg_left hMI hK, mul_le_mul_of_nonneg_left hII (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (add_nonneg (add_nonneg hD hF) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) hB)) htotal]
  · intro x
    rw [globalCauchyDerivative, norm_smul]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hDb' x) (hTb'.1 x))) hc).trans
    have hL1 := mul_le_mul_of_nonneg_left hHI hD
    have hL2 := mul_le_mul_of_nonneg_left hII hA
    have hRest := mul_nonneg (show 0 ≤ K+F+A+B+1 by positivity) htotal
    dsimp only [c, I] at *
    nlinarith
  · intro x y
    have hr : 0 ≤ ‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [globalCauchyDerivative, ← smul_sub, norm_smul]
    have he : cutoffCauchyDerivative schauderBump g x+tailCauchyDerivative g x -
        (cutoffCauchyDerivative schauderBump g y+tailCauchyDerivative g y) =
        (cutoffCauchyDerivative schauderBump g x-cutoffCauchyDerivative schauderBump g y)+
        (tailCauchyDerivative g x-tailCauchyDerivative g y) := by abel
    rw [he]
    apply (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (hFb g hgC H hH hh x y) (hTh x y))) hc).trans
    have hL1 := mul_le_mul_of_nonneg_left hHI hF
    have hL2 := mul_le_mul_of_nonneg_left hII (show 0 ≤ 2*A+B by positivity)
    have hRest := mul_nonneg (show 0 ≤ K+D+1 by positivity) htotal
    have he' : F*H+(2*A+B)*I ≤ (K+D+F+2*A+B+1)*(M+H+I) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he' hr) hc
    dsimp only [c, I] at *
    nlinarith

lemma cauchyTransform_holder_contDiff_one {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hb : ∀ x, ‖g x‖ ≤ M)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) : ContDiff ℝ 1 (cauchyTransform g) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (cauchyTransform_holder_hasFDerivAt hgC hi hH hg x).differentiableAt,?_⟩
  have he : fderiv ℝ (cauchyTransform g) = globalCauchyDerivative g :=
    funext fun x => (cauchyTransform_holder_hasFDerivAt hgC hi hH hg x).fderiv
  rw [he]
  obtain ⟨C,hC,hbnd⟩ := cauchyTransform_schauder_bounds (E := E)
  exact holder_continuous (by norm_num : (0:ℝ) < (1:ℝ)/3) (hbnd g hgC hi M H hM hH hb hg).2.2

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ} (hK : IsCompact K)
local instance : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
local instance : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance : NormedSpace ℝ (COne ℂ E) := inferInstance
include hK

omit [CompleteSpace E] in
lemma supportedHolder_hasCompactSupport (g : supportedHolder (E := E) K) :
    HasCompactSupport (valueCLM _ g.val) := by
  apply HasCompactSupport.intro hK
  exact (mem_supportedHolder g.val K).mp g.property

omit [CompleteSpace E] in
lemma supportedHolder_integrable (g : supportedHolder (E := E) K) :
    Integrable (valueCLM _ g.val) :=
  (valueCLM _ g.val).continuous.integrable_of_hasCompactSupport
    (supportedHolder_hasCompactSupport hK g)

omit [CompleteSpace E] in
lemma supportedHolder_integral_norm_le (g : supportedHolder (E := E) K) :
    (∫ x : ℂ, ‖valueCLM _ g.val x‖) ≤ ‖g‖ * volume.real K := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx => by rw [(mem_supportedHolder g.val K).mp g.property x hx, norm_zero])]
  apply le_trans (le_abs_self _)
  exact norm_setIntegral_le_of_norm_le_const (f := fun x => ‖valueCLM _ g.val x‖) hK.measure_lt_top (fun x _ => by
    rw [Real.norm_eq_abs, abs_norm]
    exact norm_value_le g.val x)

lemma supported_cauchy_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : supportedHolder (E := E) K,
    (∀ x, ‖cauchyTransform (valueCLM _ g.val) x‖ ≤ C*‖g‖) ∧
    (∀ x, ‖globalCauchyDerivative (valueCLM _ g.val) x‖ ≤ C*‖g‖) ∧
    (∀ x y, ‖globalCauchyDerivative (valueCLM _ g.val) x -
      globalCauchyDerivative (valueCLM _ g.val) y‖ ≤ C*‖g‖*‖x-y‖^((1:ℝ)/3)) := by
  obtain ⟨C,hC,hb⟩ := cauchyTransform_schauder_bounds (E := E)
  refine ⟨C*(2+volume.real K),by positivity,?_⟩
  intro g
  have hg := hb (valueCLM _ g.val) (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) ‖g‖ ‖g‖ (norm_nonneg g) (norm_nonneg g)
    (norm_value_le g.val) (by intro x y; change ‖valueCLM _ g.val x-valueCLM _ g.val y‖ ≤ ‖g.val‖*‖x-y‖^((1:ℝ)/3); simpa only [dist_eq_norm] using norm_sub_value_le g.val x y)
  have he : C*(‖g‖+‖g‖+∫ x : ℂ, ‖valueCLM _ g.val x‖) ≤ (C*(2+volume.real K))*‖g‖ := by
    have hh := mul_le_mul_of_nonneg_left (supportedHolder_integral_norm_le hK g) hC
    nlinarith
  exact ⟨fun x => (hg.1 x).trans he,fun x => (hg.2.1 x).trans he,
    fun x y => (hg.2.2 x y).trans (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (norm_nonneg _) _))⟩

private def schauderConstant : ℝ := (supported_cauchy_bounds (E := E) hK).choose
private lemma schauderConstant_nonneg : 0 ≤ schauderConstant (E := E) hK :=
  (supported_cauchy_bounds (E := E) hK).choose_spec.1
private lemma schauderConstant_spec (g : supportedHolder (E := E) K) :
    (∀ x, ‖cauchyTransform (valueCLM _ g.val) x‖ ≤ schauderConstant (E := E) hK*‖g‖) ∧
    (∀ x, ‖globalCauchyDerivative (valueCLM _ g.val) x‖ ≤ schauderConstant (E := E) hK*‖g‖) ∧
    (∀ x y, ‖globalCauchyDerivative (valueCLM _ g.val) x-globalCauchyDerivative (valueCLM _ g.val) y‖ ≤
      schauderConstant (E := E) hK*‖g‖*‖x-y‖^((1:ℝ)/3)) :=
  (supported_cauchy_bounds (E := E) hK).choose_spec.2 g

def supportedCauchy (g : supportedHolder (E := E) K) : COne ℂ E := by
  let f := cauchyTransform (valueCLM _ g.val)
  let A := globalCauchyDerivative (valueCLM _ g.val)
  let B := schauderConstant (E := E) hK * ‖g‖
  have hB : 0 ≤ B := mul_nonneg (schauderConstant_nonneg hK) (norm_nonneg g)
  have hd : ∀ x, HasFDerivAt f (A x) x :=
    cauchyTransform_holder_hasFDerivAt (valueCLM _ g.val).continuous
      (supportedHolder_integrable hK g) (norm_nonneg g.val)
      (by simpa only [dist_eq_norm] using norm_sub_value_le g.val)
  have hb := schauderConstant_spec hK g
  exact ⟨(ofBoundedDeriv f (fun x => (hd x).differentiableAt) B B hB hB hb.1
      (fun x => by rw [(hd x).fderiv]; exact hb.2.1 x),
    ofBound A (holder_continuous (by norm_num : (0:ℝ)<(1:ℝ)/3) hb.2.2)
      B B hb.2.1 hB (by simpa only [dist_eq_norm] using hb.2.2)),hd⟩

@[simp] lemma supportedCauchy_value (g : supportedHolder (E := E) K) (x : ℂ) :
    cValue (supportedCauchy hK g) x = cauchyTransform (valueCLM _ g.val) x := rfl
@[simp] lemma supportedCauchy_deriv (g : supportedHolder (E := E) K) (x : ℂ) :
    cDeriv (supportedCauchy hK g) x = globalCauchyDerivative (valueCLM _ g.val) x := rfl

lemma supportedCauchy_norm_le (g : supportedHolder (E := E) K) :
    ‖supportedCauchy hK g‖ ≤ (3*schauderConstant (E := E) hK)*‖g‖ := by
  let B := schauderConstant (E := E) hK * ‖g‖
  have hB : 0 ≤ B := mul_nonneg (schauderConstant_nonneg hK) (norm_nonneg g)
  have hd := cauchyTransform_holder_hasFDerivAt (valueCLM _ g.val).continuous
    (supportedHolder_integrable hK g) (norm_nonneg g.val)
    (by simpa only [dist_eq_norm] using norm_sub_value_le g.val)
  have hb := schauderConstant_spec hK g
  change max _ _ ≤ _
  apply max_le
  · apply (ofBoundedDeriv_norm_le _ (fun x => (hd x).differentiableAt) B B hB hB hb.1
      (fun x => by rw [(hd x).fderiv]; exact hb.2.1 x)).trans
    dsimp only [B]; linarith
  · apply (ofBound_norm_le _ _ B B hB hb.2.1 hB
      (by simpa only [dist_eq_norm] using hb.2.2)).trans
    rw [max_self]
    dsimp only [B] at *; nlinarith

omit [CompleteSpace E] in
lemma supported_cauchy_integrable (g : supportedHolder (E := E) K) (x : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ • valueCLM _ g.val (x-w)) :=
  (supportedHolder_hasCompactSupport hK g).convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv
    (valueCLM _ g.val).continuous x

lemma supportedCauchy_add (g h : supportedHolder (E := E) K) :
    supportedCauchy hK (g+h) = supportedCauchy hK g + supportedCauchy hK h := by
  apply cValue_ext
  intro x
  simp only [supportedCauchy_value, cValue_add, cauchyTransform_apply]
  change (Real.pi : ℂ)⁻¹ • (∫ w : ℂ, w⁻¹ •
    (valueCLM _ g.val (x-w)+valueCLM _ h.val (x-w))) = _
  simp_rw [smul_add]
  rw [integral_add (supported_cauchy_integrable hK g x) (supported_cauchy_integrable hK h x),smul_add]

lemma supportedCauchy_smul (c : ℝ) (g : supportedHolder (E := E) K) :
    supportedCauchy hK (c • g) = c • supportedCauchy hK g := by
  apply cValue_ext
  intro x
  simp only [supportedCauchy_value, cValue_smul, cauchyTransform_apply]
  change (Real.pi : ℂ)⁻¹ • (∫ w : ℂ, w⁻¹ • (c • valueCLM _ g.val (x-w))) = _
  simp_rw [smul_comm (M := ℂ) (N := ℝ)]
  rw [integral_smul]
  exact smul_comm _ _ _

def supportedCauchyCLM : supportedHolder (E := E) K →L[ℝ] COne ℂ E :=
  LinearMap.mkContinuous
    { toFun := supportedCauchy hK
      map_add' := supportedCauchy_add hK
      map_smul' := supportedCauchy_smul hK }
    (3*schauderConstant hK) (supportedCauchy_norm_le hK)

@[simp] lemma supportedCauchyCLM_value (g : supportedHolder (E := E) K) (x : ℂ) :
    cValue (supportedCauchyCLM hK g) x = cauchyTransform (valueCLM _ g.val) x := rfl

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
