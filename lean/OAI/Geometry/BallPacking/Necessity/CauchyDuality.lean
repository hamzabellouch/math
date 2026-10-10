import Mathlib
import OAI.Geometry.BallPacking.Cauchy.GreenFormula
import OAI.Geometry.BallPacking.Necessity.KernelMoments

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset

open scoped ContDiff Topology
open Set Filter MeasureTheory
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma annularPotential_difference (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M)
    (j : ℕ) (x : ℂ) :
    scaledKernelPotential (annularCauchyKernel b) (((1:ℝ)/8)^j) g x =
      scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x-
      scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^(j+1)) g x := by
  rw [scaledKernel_asConvolution _ (by positivity),
    scaledKernel_asConvolution _ (by positivity),scaledKernel_asConvolution _ (by positivity)]
  have hi (k : ℕ) : Integrable (fun w : ℂ =>
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^k) w • g (x-w)) :=
    (physicalScaledKernel_integrable (cutoffCauchyKernel_integrableNecessity b) (by positivity)).smul_bdd M
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun w => hM (x-w))
  simp only [MeasureTheory.convolution,ContinuousLinearMap.lsmul_apply,physicalScaled_annular,
    sub_smul]
  exact integral_sub (hi j) (hi (j+1))

omit [CompleteSpace E] in
lemma cutoffPotential_scale_zero (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    Tendsto (fun j : ℕ => scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j => scaledKernel_value_bound_integrable
    (cutoffCauchyKernel_integrableNecessity b) (ε := ((1:ℝ)/8)^j) (by positivity) hM x)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (by norm_num : ‖(1:ℝ)/8‖ < 1)).const_mul ((∫ w : ℂ, ‖cutoffCauchyKernel b w‖)*M)

 
lemma dyadicKernel_cutoff_identity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    dyadicKernelPotential (annularCauchyKernel b) g =
      MeasureTheory.convolution (cutoffCauchyKernel b) g (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
  funext x
  let v (j : ℕ) := scaledKernelPotential (cutoffCauchyKernel b) (((1:ℝ)/8)^j) g x
  have he (n : ℕ) : (∑ j ∈ Finset.range n,
      scaledKernelPotential (annularCauchyKernel b) (((1:ℝ)/8)^j) g x) = v 0-v n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,annularPotential_difference b hg hM n x]
      change v 0-v n+(v n-v (n+1))=v 0-v (n+1)
      abel
  have ht := (dyadicKernel_value_summable (annularCauchyKernel_smooth b).continuous
    (annularCauchyKernel_compactSupport b) hM x).hasSum.tendsto_sum_nat
  have ht' : Tendsto (fun n => v 0-v n) atTop (𝓝 (v 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (cutoffPotential_scale_zero b hM x)
  have hu : dyadicKernelPotential (annularCauchyKernel b) g x = v 0 :=
    tendsto_nhds_unique ht (ht'.congr (fun n => (he n).symm))
  rw [hu]
  simp only [v,pow_zero,scaledKernelPotential,inv_one,one_smul]

 
theorem cutoffCauchy_contDiff_oneNecessity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) := by
  rw [←dyadicKernel_cutoff_identity b hg hM]
  exact dyadicKernel_contDiff_one (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hM hH hHg

theorem cutoffCauchy_hasFDerivAtNecessity (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume)
      (dyadicKernelDerivative (annularCauchyKernel b) g x) x := by
  rw [←dyadicKernel_cutoff_identity b hg hM]
  exact dyadicKernel_hasFDerivAt (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hM hH hHg x

theorem cutoffCauchy_fderiv_holder (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) x-
      fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
        H*(kernelMomentTwo (annularCauchyKernel b)+8*kernelMomentOne (annularCauchyKernel b))*
          ‖x-y‖^((1:ℝ)/3) := by
  rw [(cutoffCauchy_hasFDerivAtNecessity b hg hM hH hHg x).fderiv,
    (cutoffCauchy_hasFDerivAtNecessity b hg hM hH hHg y).fderiv]
  exact dyadicKernel_derivative_holder (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hH hHg x y

end

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem cutoff_cauchy_supported_eq (b : ContDiffBump (0:ℂ)) {R : ℝ}
    (hR : 2*R ≤ b.rIn) {g : ℂ → E} (hs : tsupport g ⊆ Metric.closedBall (0:ℂ) R)
    {x : ℂ} (hx : x ∈ Metric.closedBall (0:ℂ) R) :
    convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x =
      convolution (fun w : ℂ => w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  change (b w • w⁻¹) • g (x-w)=w⁻¹ • g (x-w)
  by_cases hg : g (x-w)=0
  · rw [hg,smul_zero,smul_zero]
  have hw : x-w ∈ Metric.closedBall (0:ℂ) R := hs (subset_tsupport g (by exact hg))
  have hw' : w ∈ Metric.closedBall (0:ℂ) b.rIn := by
    rw [Metric.mem_closedBall,dist_zero_right]
    have hn : ‖w‖ ≤ ‖x‖+‖x-w‖ := by
      convert norm_sub_le x (x-w) using 1
      simp only [sub_sub_cancel]
    have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hw'' : ‖x-w‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    linarith
  rw [b.one_of_mem_closedBall hw',one_smul]

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma cauchyTransform_eventually_cutoff {g : ℂ → E} {S : ℝ}
    (hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) S) (b : ContDiffBump (0:ℂ))
    (hb : 2*S ≤ b.rIn) {x : ℂ} (hx : ‖x‖ < S) :
    cauchyTransform g =ᶠ[𝓝 x] fun z => (Real.pi:ℂ)⁻¹ •
      MeasureTheory.convolution (cutoffCauchyKernel b) g (ContinuousLinearMap.lsmul ℝ ℂ) volume z := by
  filter_upwards [Metric.closedBall_mem_nhds_of_mem (show x ∈ Metric.ball (0:ℂ) S by
    simpa only [Metric.mem_ball,dist_zero_right] using hx)] with z hz
  exact congrArg ((Real.pi:ℂ)⁻¹ • ·) (cutoff_cauchy_supported_eq b hb hgs hz).symm

 
theorem cauchyTransform_holder_contDiff_oneNecessity {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (cauchyTransform g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) S :=
    hR.trans (Metric.closedBall_subset_closedBall hRS)
  exact ((cutoffCauchy_contDiff_oneNecessity b hg hM hH hHg).const_smul (Real.pi:ℂ)⁻¹).contDiffAt
    |>.congr_of_eventuallyEq (cauchyTransform_eventually_cutoff hgs b (le_refl _) hxS)

 
theorem cauchyTransform_fderiv_holder_on (S : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → E), Continuous g →
      tsupport g ⊆ Metric.closedBall (0:ℂ) S → ∀ M H : ℝ,
      (∀ x, ‖g x‖ ≤ M) → 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) →
      ∀ x ∈ Metric.closedBall (0:ℂ) S, ∀ y ∈ Metric.closedBall (0:ℂ) S,
      ‖fderiv ℝ (cauchyTransform g) x-fderiv ℝ (cauchyTransform g) y‖ ≤
        C*H*‖x-y‖^((1:ℝ)/3) := by
  let T : ℝ := max S 0+1
  have hST : S < T := by dsimp [T]; linarith [le_max_left S 0]
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right S 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*T,2*T+1,by positivity,by linarith⟩
  let C : ℝ := Real.pi⁻¹*(kernelMomentTwo (annularCauchyKernel b)+
    8*kernelMomentOne (annularCauchyKernel b))
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (add_nonneg (kernelMomentTwo_nonneg _) (mul_nonneg (by norm_num) (kernelMomentOne_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro g hg hgs M H hM hH hHg x hx y hy
  have hgs' : tsupport g ⊆ Metric.closedBall (0:ℂ) T :=
    hgs.trans (Metric.closedBall_subset_closedBall hST.le)
  have hd (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) S) :
      fderiv ℝ (cauchyTransform g) z = (Real.pi:ℂ)⁻¹ •
        fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) z := by
    have hzS : ‖z‖ ≤ S := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hzT : ‖z‖ < T := hzS.trans_lt hST
    have hder := ((cutoffCauchy_contDiff_oneNecessity b hg hM hH hHg).differentiable (by simp) z).hasFDerivAt
    exact ((hder.const_smul (Real.pi:ℂ)⁻¹).congr_of_eventuallyEq
      (cauchyTransform_eventually_cutoff hgs' b (le_refl _) hzT)).fderiv
  rw [hd x hx,hd y hy,←smul_sub,norm_smul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  exact (mul_le_mul_of_nonneg_left (cutoffCauchy_fderiv_holder b hg hM hH hHg x y)
    (inv_nonneg.mpr Real.pi_pos.le)).trans_eq (by dsimp [C]; ring)

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section

lemma compactKernel_convolution_tendsto_bounded
    {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : A →L[ℝ] E →L[ℝ] F) {K : ℂ → A} (hK : Continuous K) (hc : HasCompactSupport K)
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E}
    (hv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (x : ℂ) :
    Tendsto (fun j => MeasureTheory.convolution K (g j) L volume x) atTop
      (𝓝 (MeasureTheory.convolution K v L volume x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun w : ℂ => ‖L‖*‖K w‖*M)
  · apply Eventually.of_forall
    intro j
    exact ((L.continuous.comp hK).clm_apply
      ((hg j).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro j
    apply ae_of_all
    intro w
    exact (L.le_opNorm₂ (K w) (g j (x-w))).trans
      (mul_le_mul_of_nonneg_left (hM j (x-w)) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg L) (norm_nonneg (K w))))
  · exact ((hK.integrable_of_hasCompactSupport hc).norm.const_mul ‖L‖).mul_const M
  · apply ae_of_all
    intro w
    exact ((L (K w)).continuous.tendsto _).comp (hv (x-w))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma scaledKernelDerivative_tendsto {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (ε : ℝ) (x : ℂ) :
    Tendsto (fun j => scaledKernelDerivative K ε (g j) x) atTop
      (𝓝 (scaledKernelDerivative K ε v x)) := by
  have he {f : ℂ → E} (hf : Continuous f) : scaledKernelDerivative K ε f x =
      MeasureTheory.convolution (fderiv ℝ K) (fun w => f (ε • w))
        ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) volume (ε⁻¹ • x) := by
    have hfe : Continuous (fun w : ℂ => f (ε • w)) := by fun_prop
    exact (hc.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
      (hK.of_le (by simp)) hfe.locallyIntegrable (ε⁻¹ • x)).fderiv
  simp_rw [he hv,he (hg _)]
  exact compactKernel_convolution_tendsto_bounded ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ)
    (hK.continuous_fderiv (by simp)) (hc.fderiv ℝ) (fun j => by fun_prop)
    (fun w => hgv (ε • w)) (fun j w => hM j (ε • w)) (ε⁻¹ • x)

lemma dyadicKernelDerivative_tendsto {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => dyadicKernelDerivative K (g j) x) atTop (𝓝 (dyadicKernelDerivative K v x)) := by
  apply tendsto_tsum_of_dominated_convergence (dyadic_summable.mul_left (H*kernelMomentOne K))
  · intro k
    exact scaledKernelDerivative_tendsto hK hc hg hv hgv hM _ x
  · apply Eventually.of_forall
    intro j k
    exact dyadicKernel_derivative_bound hK hc (hg j) hH (hHg j) k x

lemma cutoffCauchy_fderiv_tendsto (b : ContDiffBump (0:ℂ))
    {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j)) {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w)))
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hMv : ∀ w, ‖v w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    (hHv : ∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) (g j)
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) atTop
      (𝓝 (fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) v
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x)) := by
  simp_rw [(cutoffCauchy_hasFDerivAtNecessity b hv hMv hH hHv x).fderiv,
    (cutoffCauchy_hasFDerivAtNecessity b (hg _) (hM _) hH (hHg _) x).fderiv]
  exact dyadicKernelDerivative_tendsto (annularCauchyKernel_smooth b)
    (annularCauchyKernel_compactSupport b) hg hv hgv hM hH hHg x

 

theorem cauchyTransform_fderiv_tendsto {g : ℕ → ℂ → E} (hg : ∀ j, Continuous (g j))
    {v : ℂ → E} (hv : Continuous v)
    (hgv : ∀ w, Tendsto (fun j => g j w) atTop (𝓝 (v w))) {R : ℝ}
    (hgs : ∀ j, tsupport (g j) ⊆ Metric.closedBall (0:ℂ) R)
    (hvs : tsupport v ⊆ Metric.closedBall (0:ℂ) R)
    {M H : ℝ} (hM : ∀ j w, ‖g j w‖ ≤ M) (hMv : ∀ w, ‖v w‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ j x y, ‖g j x-g j y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    (hHv : ∀ x y, ‖v x-v y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun j => fderiv ℝ (cauchyTransform (g j)) x) atTop
      (𝓝 (fderiv ℝ (cauchyTransform v) x)) := by
  let S : ℝ := max R 0+‖x‖+1
  have hRS : R ≤ S := by dsimp [S]; linarith [le_max_left R 0,norm_nonneg x]
  have hS : 0 < S := by dsimp [S]; linarith [le_max_right R 0,norm_nonneg x]
  have hxS : ‖x‖ < S := by dsimp [S]; linarith [le_max_right R 0]
  let b : ContDiffBump (0:ℂ) := ⟨2*S,2*S+1,by positivity,by linarith⟩
  have he {f : ℂ → E} (hf : Continuous f)
      (hs : tsupport f ⊆ Metric.closedBall (0:ℂ) R) (hm : ∀ z, ‖f z‖ ≤ M)
      (hh : ∀ z w, ‖f z-f w‖ ≤ H*‖z-w‖^((1:ℝ)/3)) :
      fderiv ℝ (cauchyTransform f) x = (Real.pi:ℂ)⁻¹ •
        fderiv ℝ (MeasureTheory.convolution (cutoffCauchyKernel b) f
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) x := by
    have hder := ((cutoffCauchy_contDiff_oneNecessity b hf hm hH hh).differentiable (by simp) x).hasFDerivAt
    exact ((hder.const_smul (Real.pi:ℂ)⁻¹).congr_of_eventuallyEq
      (cauchyTransform_eventually_cutoff (hs.trans (Metric.closedBall_subset_closedBall hRS))
        b (le_refl _) hxS)).fderiv
  simp_rw [he hv hvs hMv hHv,he (hg _) (hgs _) (hM _) (hHg _)]
  exact (cutoffCauchy_fderiv_tendsto b hg hv hgv hM hMv hH hHg hHv x).const_smul (Real.pi:ℂ)⁻¹

end

 

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def holderMollify (b : ContDiffBump (0:ℂ)) (g : ℂ → E) : ℂ → E :=
  MeasureTheory.convolution (b.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

omit [CompleteSpace E] in
lemma holderMollify_smooth (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g) :
    ContDiff ℝ ∞ (holderMollify b g) :=
  b.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    b.contDiff_normed hg.locallyIntegrable

omit [CompleteSpace E] in
lemma holderMollify_bound (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) : ‖holderMollify b g x‖ ≤ M := by
  change ‖∫ w : ℂ, b.normed volume w • g (x-w)‖ ≤ M
  have hb : ∀ w : ℂ, ‖b.normed volume w • g (x-w)‖ ≤ b.normed volume w*M := by
    intro w
    rw [norm_smul,Real.norm_of_nonneg (b.nonneg_normed w)]
    exact mul_le_mul_of_nonneg_left (hM _) (b.nonneg_normed w)
  exact (norm_integral_le_of_norm_le (b.integrable_normed.mul_const M) (ae_of_all _ hb)).trans_eq
    (by rw [integral_mul_const,b.integral_normed,one_mul])

omit [CompleteSpace E] in
lemma holderMollify_holder (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g)
    {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖holderMollify b g x-holderMollify b g y‖ ≤ H*‖x-y‖^((1:ℝ)/3) := by
  have hi (z : ℂ) : Integrable (fun w : ℂ => b.normed volume w • g (z-w)) :=
    b.integrable_normed.smul_bdd M (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun w => hM _)
  change ‖(∫ w : ℂ, b.normed volume w • g (x-w))-
    (∫ w : ℂ, b.normed volume w • g (y-w))‖ ≤ _
  rw [←integral_sub (hi x) (hi y)]
  have hb : ∀ w : ℂ, ‖b.normed volume w • g (x-w)-b.normed volume w • g (y-w)‖ ≤
      b.normed volume w*(H*‖x-y‖^((1:ℝ)/3)) := by
    intro w
    rw [←smul_sub,norm_smul,Real.norm_of_nonneg (b.nonneg_normed w)]
    exact mul_le_mul_of_nonneg_left (by simpa only [sub_sub_sub_cancel_right] using hHg (x-w) (y-w))
      (b.nonneg_normed w)
  exact (norm_integral_le_of_norm_le
    (b.integrable_normed.mul_const (H*‖x-y‖^((1:ℝ)/3))) (ae_of_all _ hb)).trans_eq
      (by rw [integral_mul_const,b.integral_normed,one_mul])

omit [CompleteSpace E] in
lemma holderMollify_support (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {R : ℝ}
    (hgs : tsupport g ⊆ Metric.closedBall (0:ℂ) R) :
    tsupport (holderMollify b g) ⊆ Metric.closedBall (0:ℂ) (b.rOut+R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hs := MeasureTheory.support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) (f := b.normed volume) (g := g) hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hs
  have hw' : ‖w‖ ≤ b.rOut := by
    have hh := subset_tsupport (b.normed volume) hw
    rw [b.tsupport_normed_eq] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh
  have hz' : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hgs (subset_tsupport g hz)
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    (norm_add_le w z).trans (add_le_add hw' hz')

omit [CompleteSpace E] in
lemma holderMollify_compactSupport (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hc : HasCompactSupport g) : HasCompactSupport (holderMollify b g) :=
  b.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hc

def shrinkingHolderBump (j : ℕ) : ContDiffBump (0:ℂ) :=
  ⟨(((1:ℝ)/2)^j)/2,((1:ℝ)/2)^j,by positivity,by
    have h : 0 < ((1:ℝ)/2)^j := by positivity
    linarith⟩

lemma shrinkingHolderBump_radius_le (j : ℕ) : (shrinkingHolderBump j).rOut ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma holderMollify_tendsto {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Tendsto (fun j : ℕ => holderMollify (shrinkingHolderBump j) g x) atTop (𝓝 (g x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1:ℝ)/2‖ < 1)) hg x

end

open scoped ContDiff Topology Classical
open Set Function Filter MeasureTheory

 
 

 

open scoped ContDiff Topology
open Set Function MeasureTheory

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem cauchyCurl_subLeft {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (z w : ℂ) :
    cauchyCurl (fun v => g (z-v)) w = -cauchyCurl g (z-w) := by
  have hd := ((hg.differentiable (by simp) (z-w)).hasFDerivAt).comp w
    ((hasFDerivAt_const z w).sub (hasFDerivAt_id w))
  change HasFDerivAt (fun v => g (z-v)) _ w at hd
  simp [cauchyCurl,hd.fderiv]
  ring

 theorem cauchy_integral_curl_translate {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    (∫ w : ℂ, w⁻¹ * cauchyCurl g (z-w)) = (2*Real.pi*Complex.I)*g z := by
  have hs : ContDiff ℝ ∞ (fun w => g (z-w)) := hg.comp (contDiff_const.sub contDiff_id)
  have hsc : HasCompactSupport (fun w => g (z-w)) :=
    hc.comp_homeomorph (Homeomorph.subLeft z)
  have hh := cauchy_green_fundamental hs hsc
  simp_rw [cauchyCurl_subLeft hg,neg_div,div_eq_mul_inv,mul_comm (cauchyCurl g (z-_)),
    integral_neg,sub_zero] at hh
  linear_combination -hh

 theorem cauchyTransform_curl {g : ℂ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    cauchyCurl (cauchyTransform g) z = (2*Complex.I)*g z := by
  have hd := cauchyTransform_hasFDerivAt hc hg z
  have hD : Continuous (fderiv ℝ g) := (hg.fderiv_right (m := ∞) (by simp)).continuous
  have hi (v : ℂ) : Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ g (z-w) v) := by
    exact (hc.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_complex_inv
        ((ContinuousLinearMap.apply ℝ ℂ v).continuous.comp hD) z
  rw [cauchyCurl,hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℂ)
      locallyIntegrable_complex_inv (hc.fderiv (𝕜 := ℝ)) hD,
    convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℂ)
      locallyIntegrable_complex_inv (hc.fderiv (𝕜 := ℝ)) hD]
  change Complex.I*((Real.pi:ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * fderiv ℝ g (z-w) 1) -
      (Real.pi:ℂ)⁻¹ * (∫ w : ℂ, w⁻¹ * fderiv ℝ g (z-w) Complex.I) = _
  calc
    _ = (Real.pi:ℂ)⁻¹ * (∫ w : ℂ, w⁻¹ * cauchyCurl g (z-w)) := by
      rw [show (fun w : ℂ => w⁻¹*cauchyCurl g (z-w)) =
        (fun w => Complex.I*(w⁻¹*fderiv ℝ g (z-w) 1) - w⁻¹*fderiv ℝ g (z-w) Complex.I) from
        funext (fun w => by dsimp only [cauchyCurl]; ring)]
      rw [integral_sub ((hi 1).const_mul _) (hi Complex.I),integral_const_mul]
      ring
    _ = _ := by
      rw [cauchy_integral_curl_translate hg hc]
      field_simp [Real.pi_ne_zero]


open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 

theorem cauchyTransform_holder_curlNecessity {g : ℂ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) {M H : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    cauchyCurl (cauchyTransform g) x = (2*Complex.I)*g x := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
  let u (j : ℕ) := holderMollify (shrinkingHolderBump j) g
  have hus (j : ℕ) : ContDiff ℝ ∞ (u j) := holderMollify_smooth _ hg
  have huc (j : ℕ) : HasCompactSupport (u j) := holderMollify_compactSupport _ hc
  have huM (j : ℕ) (w : ℂ) : ‖u j w‖ ≤ M := holderMollify_bound _ hM w
  have huH (j : ℕ) (w z : ℂ) : ‖u j w-u j z‖ ≤ H*‖w-z‖^((1:ℝ)/3) :=
    holderMollify_holder _ hg hM hHg w z
  have huR (j : ℕ) : tsupport (u j) ⊆ Metric.closedBall (0:ℂ) (R+1) :=
    (holderMollify_support _ hR).trans (Metric.closedBall_subset_closedBall (by
      linarith [shrinkingHolderBump_radius_le j]))
  have hgR : tsupport g ⊆ Metric.closedBall (0:ℂ) (R+1) :=
    hR.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hd := cauchyTransform_fderiv_tendsto (fun j => (hus j).continuous) hg
    (holderMollify_tendsto hg) huR hgR huM hM hH huH hHg x
  have hde (z : ℂ) := ((ContinuousLinearMap.apply ℝ ℂ z).continuous.tendsto _).comp hd
  have hl : Tendsto (fun j => cauchyCurl (cauchyTransform (u j)) x) atTop
      (𝓝 (cauchyCurl (cauchyTransform g) x)) :=
    ((hde 1).const_mul Complex.I).sub (hde Complex.I)
  have he : (fun j => cauchyCurl (cauchyTransform (u j)) x) =
      (fun j => (2*Complex.I)*u j x) := funext fun j => cauchyTransform_curl (hus j) (huc j) x
  rw [he] at hl
  exact tendsto_nhds_unique hl ((holderMollify_tendsto hg x).const_mul (2*Complex.I))


 

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 def complexCauchyCurl (g : ℂ → E) (z : ℂ) : E :=
  Complex.I • fderiv ℝ g z 1 - fderiv ℝ g z Complex.I

 theorem complexCauchyCurl_smooth {g : ℂ → E} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (complexCauchyCurl g) := by
  exact (((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).const_smul _).sub
    ((hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

 theorem complexCauchyCurl_compactSupport {g : ℂ → E} (hg : HasCompactSupport g) :
    HasCompactSupport (complexCauchyCurl g) :=
  ((hg.fderiv_apply (𝕜 := ℝ) 1).comp_left (smul_zero Complex.I)).sub
    (hg.fderiv_apply (𝕜 := ℝ) Complex.I)

 theorem complexCauchyCurl_dual {g : ℂ → E} (hg : Differentiable ℝ g)
    (l : E →L[ℂ] ℂ) (z : ℂ) :
    l (complexCauchyCurl g z) = cauchyCurl (fun w => l (g w)) z := by
  have hd := (l.restrictScalars ℝ).hasFDerivAt.comp z (hg z).hasFDerivAt
  change HasFDerivAt (fun w => l (g w)) _ z at hd
  simp only [complexCauchyCurl,map_sub,map_smul,cauchyCurl,hd.fderiv]
  rfl

 theorem cauchyTransform_dual [CompleteSpace E] {g : ℂ → E} (hg : Continuous g)
    (hc : HasCompactSupport g) (l : E →L[ℂ] ℂ) (z : ℂ) :
    l (cauchyTransform g z) = cauchyTransform (fun w => l (g w)) z := by
  have hi := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_complex_inv hg z
  have hi' : Integrable (fun w : ℂ => w⁻¹ • g (z-w)) := hi
  simp only [cauchyTransform_apply,map_smul]
  congr 1
  simpa only [map_smul] using (l.integral_comp_comm hi').symm

end HigherDimensionalBallPacking.Rigidity

end

namespace SymplecticBallPacking.Hamiltonian
-- Preserve the namespace exported by this module.
end SymplecticBallPacking.Hamiltonian

end OAI
