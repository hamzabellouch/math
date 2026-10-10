import Mathlib
import OAI.Geometry.BallPacking.Holder.NonlinearCR

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory

open scoped ContDiff Topology
open Set Filter MeasureTheory
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def kernelMomentOne (K : ℂ → ℂ) : ℝ :=
  ∫ w : ℂ, ‖fderiv ℝ K w‖ * ‖w‖^((1:ℝ)/3)
def kernelMomentTwo (K : ℂ → ℂ) : ℝ :=
  ∫ w : ℂ, ‖fderiv ℝ (fderiv ℝ K) w‖ * ‖w‖^((1:ℝ)/3)

lemma weightedKernel_integrable {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun w : ℂ => ‖f w‖*‖w‖^((1:ℝ)/3)) := by
  exact (hf.norm.mul (continuous_norm.rpow_const (fun _ => Or.inr (by norm_num)))).integrable_of_hasCompactSupport
    (hc.norm.mul_right)

lemma kernelMomentOne_nonneg (K : ℂ → ℂ) : 0 ≤ kernelMomentOne K :=
  integral_nonneg (fun _ => by positivity)
lemma kernelMomentTwo_nonneg (K : ℂ → ℂ) : 0 ≤ kernelMomentTwo K :=
  integral_nonneg (fun _ => by positivity)

lemma compactKernel_schauder_first {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (_hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x‖ ≤
      H*kernelMomentOne K := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hb : ∀ x w v : ℂ,
      ‖fderiv ℝ K w v‖*‖g (x-w)-g x‖ ≤ (H*(‖fderiv ℝ K w‖*‖w‖^((1:ℝ)/3)))*‖v‖ := by
    intro x w v
    have hh : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left,norm_neg] using hHg (x-w) x
    calc
      _ ≤ (‖fderiv ℝ K w‖*‖v‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul (ContinuousLinearMap.le_opNorm _ _) hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  apply (compact_kernel_convolution_derivative_bound hK hc hg
    ((weightedKernel_integrable hd.continuous (hc.fderiv ℝ)).const_mul H) hb x).trans_eq
  rw [integral_const_mul]
  rfl

omit [CompleteSpace E] in
lemma compactKernel_directional_eq {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      convolution (fun w => fderiv ℝ K w v) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x :=
  compact_kernel_convolution_fderiv hK hc hg x v

lemma kernelMomentOne_directional_le {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (v : ℂ) :
    kernelMomentOne (fun w => fderiv ℝ K w v) ≤ kernelMomentTwo K*‖v‖ := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ K) := hK.fderiv_right (by simp)
  have hd₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ K)) := hd.fderiv_right (by simp)
  have hLv : ContDiff ℝ ∞ (fun w => fderiv ℝ K w v) := hd.clm_apply contDiff_const
  have hcv := hc.fderiv_apply (𝕜 := ℝ) v
  have hb (w : ℂ) : ‖fderiv ℝ (fun z => fderiv ℝ K z v) w‖ ≤
      ‖fderiv ℝ (fderiv ℝ K) w‖*‖v‖ := by
    rw [((hd.differentiable (by simp) w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)).fderiv]
    simp only [ContinuousLinearMap.comp_zero,zero_add]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    change ‖fderiv ℝ (fderiv ℝ K) w y v‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ K) w y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ K) w‖*‖y‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring

  calc
    _ ≤ ∫ w : ℂ, (‖fderiv ℝ (fderiv ℝ K) w‖*‖w‖^((1:ℝ)/3))*‖v‖ := by
      apply integral_mono
        (weightedKernel_integrable (hLv.fderiv_right (m := ∞) (by simp)).continuous (hcv.fderiv ℝ))
        ((weightedKernel_integrable hd₂.continuous ((hc.fderiv ℝ).fderiv ℝ)).mul_const _)
      intro w
      exact (mul_le_mul_of_nonneg_right (hb w) (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
    _ = _ := integral_mul_const _ _

lemma compactKernel_schauder_second {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
      fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      H*kernelMomentTwo K*‖x-y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [kernelMomentTwo_nonneg K])
  intro v
  simp only [sub_apply]
  rw [compactKernel_directional_eq hK hc hg,compactKernel_directional_eq hK hc hg]
  let Kv : ℂ → ℂ := fun w => fderiv ℝ K w v
  have hKv : ContDiff ℝ ∞ Kv := (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcKv : HasCompactSupport Kv := hc.fderiv_apply (𝕜 := ℝ) v
  have hbound (z : ℂ) : ‖fderiv ℝ (convolution Kv g (ContinuousLinearMap.lsmul ℝ ℂ) volume) z‖ ≤
      H*kernelMomentTwo K*‖v‖ := by
    exact (compactKernel_schauder_first hKv hcKv hg hH hHg z).trans
      ((mul_le_mul_of_nonneg_left (kernelMomentOne_directional_le hK hc v) hH).trans_eq (by ring))
  have hi := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (s := (univ : Set ℂ)) (fun z _ =>
      (hcKv.hasFDerivAt_convolution_left _ (hKv.of_le (by simp)) hg.locallyIntegrable z).differentiableAt)
    (fun z _ => hbound z) convex_univ (mem_univ y) (mem_univ x)
  exact hi.trans_eq (by ring)

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

def scaledKernelPotential (K : ℂ → ℂ) (ε : ℝ) (g : ℂ → E) (x : ℂ) : E :=
  ε • convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)

def scaledKernelDerivative (K : ℂ → ℂ) (ε : ℝ) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  fderiv ℝ (convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume) (ε⁻¹ • x)

omit [CompleteSpace E] in
lemma scaledKernel_hasFDerivAt {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : ε ≠ 0) {g : ℂ → E}
    (hg : Continuous g) (x : ℂ) :
    HasFDerivAt (scaledKernelPotential K ε g) (scaledKernelDerivative K ε g x) x := by
  have hgε : Continuous (fun z : ℂ => g (ε • z)) := by fun_prop
  have hd := hc.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
    (hK.of_le (by simp)) hgε.locallyIntegrable (ε⁻¹ • x)
  have hd' := (hd.comp x ((hasFDerivAt_id x).const_smul ε⁻¹)).const_smul ε
  have he : ε • (fderiv ℝ (convolution K (fun z => g (ε • z))
      (ContinuousLinearMap.lsmul ℝ ℂ) volume) (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ) = scaledKernelDerivative K ε g x := by
    ext v
    simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul,
      smul_smul,mul_inv_cancel₀ hε,one_smul,scaledKernelDerivative]
  rw [←hd.fderiv] at hd'
  rw [he] at hd'
  exact hd'

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma scaled_holder_bound {g : ℂ → E} {H ε : ℝ} (hε : 0 ≤ ε)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖g (ε • x)-g (ε • y)‖ ≤ (H*ε^((1:ℝ)/3))*‖x-y‖^((1:ℝ)/3) := by
  have h := hHg (ε • x) (ε • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg hε,Real.mul_rpow hε (norm_nonneg _)] at h
  exact h.trans_eq (by ring)

lemma scaledKernel_derivative_bound {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    ‖scaledKernelDerivative K ε g x‖ ≤ (H*kernelMomentOne K)*ε^((1:ℝ)/3) := by
  have hd := compactKernel_schauder_first hK hc
    (g := fun z : ℂ => g (ε • z)) (by fun_prop)
    (mul_nonneg hH (Real.rpow_nonneg hε ((1:ℝ)/3))) (scaled_holder_bound hε hHg) (ε⁻¹ • x)
  exact hd.trans_eq (by ring)

lemma scaledKernel_derivative_lipschitz {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 < ε) {g : ℂ → E}
    (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖scaledKernelDerivative K ε g x-scaledKernelDerivative K ε g y‖ ≤
      (H*kernelMomentTwo K)*(ε^((1:ℝ)/3)*ε⁻¹)*‖x-y‖ := by
  have hd := compactKernel_schauder_second hK hc
    (g := fun z : ℂ => g (ε • z)) (by fun_prop)
    (mul_nonneg hH (Real.rpow_nonneg hε.le ((1:ℝ)/3))) (scaled_holder_bound hε.le hHg) (ε⁻¹ • x) (ε⁻¹ • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)] at hd
  exact hd.trans_eq (by ring)

omit [CompleteSpace E] in
lemma scaledKernel_value_bound {K : ℂ → ℂ} (hK : Continuous K)
    (hc : HasCompactSupport K) {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖scaledKernelPotential K ε g x‖ ≤ ((∫ w : ℂ, ‖K w‖)*M)*ε := by
  rw [scaledKernelPotential,norm_smul,Real.norm_of_nonneg hε]
  have hb : ‖convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)‖ ≤
      (∫ w : ℂ, ‖K w‖)*M := by
    have hin : ∀ w : ℂ, ‖K w • g (ε • (ε⁻¹ • x-w))‖ ≤ ‖K w‖*M := by
      intro w
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    apply (norm_integral_le_of_norm_le ((hK.integrable_of_hasCompactSupport hc).norm.mul_const M)
      (Eventually.of_forall hin)).trans_eq
    exact integral_mul_const _ _
  exact (mul_le_mul_of_nonneg_left hb hε).trans_eq (by ring)

lemma eighth_rpow_third (j : ℕ) : (((1:ℝ)/8)^j)^((1:ℝ)/3)=((1:ℝ)/2)^j := by
  have hbase : ((1:ℝ)/8)^((1:ℝ)/3)=(1:ℝ)/2 := by
    have h := Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤1/2) (by decide : (3:ℕ)≠0)
    norm_num at h ⊢
  rw [←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num),Real.rpow_natCast,hbase]

lemma eighth_scale_lipschitz (j : ℕ) :
    ((((1:ℝ)/8)^j)^((1:ℝ)/3))*(((1:ℝ)/8)^j)⁻¹=(4:ℝ)^j := by
  rw [eighth_rpow_third,←inv_pow,←mul_pow]
  norm_num

end

open scoped ContDiff Topology
open Set Filter MeasureTheory

 
def annularCauchyKernel (b : ContDiffBump (0:ℂ)) (z : ℂ) : ℂ :=
  (b z-b ((8:ℝ) • z)) • z⁻¹

lemma annularCauchyKernel_smooth (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (annularCauchyKernel b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z=0
  · subst z
    have h0 : ContDiffAt ℝ ∞ (fun _ : ℂ => (0:ℂ)) 0 := contDiffAt_const
    apply h0.congr_of_eventuallyEq
    have ht : Tendsto (fun z : ℂ => (8:ℝ) • z) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun z : ℂ => (8:ℝ) • z) := by fun_prop
      simpa only [smul_zero] using hcont.tendsto (0:ℂ)
    filter_upwards [b.eventuallyEq_one, ht.eventually b.eventuallyEq_one] with w hw hw'
    simp only [annularCauchyKernel,hw,hw',Pi.one_apply,sub_self,zero_smul]
  · exact (b.contDiff.contDiffAt.sub
      (b.contDiff.comp (contDiff_id.const_smul (8:ℝ))).contDiffAt).smul
      (contDiffAt_id.inv hz)

lemma annularCauchyKernel_compactSupport (b : ContDiffBump (0:ℂ)) :
    HasCompactSupport (annularCauchyKernel b) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:ℂ) b.rOut)
  intro z hz
  have hz' : b.rOut < ‖z‖ := by
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hz8 : b.rOut ≤ ‖(8:ℝ) • z‖ := by
    rw [norm_smul]
    norm_num
    linarith [norm_nonneg z]
  rw [annularCauchyKernel,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz'.le),
    b.zero_of_le_dist (by simpa only [dist_zero_right] using hz8),sub_self,zero_smul]


 

open scoped Topology
open Set Filter Finset
section
variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [CompleteSpace F]

lemma dyadic_summable : Summable (fun j : ℕ => ((1:ℝ)/2)^j) :=
  summable_geometric_of_norm_lt_one (by norm_num)

lemma dyadic_tsum : (∑' j : ℕ, ((1:ℝ)/2)^j) = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1:ℝ)/2‖<1)]
  norm_num

lemma four_pow_sum_le (N : ℕ) : ∑ j ∈ range N, (4:ℝ)^j ≤ 4^N := by
  induction N with
  | zero => norm_num
  | succ N h =>
    rw [sum_range_succ,pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤4) N]

omit [PseudoMetricSpace X] in
lemma dyadicSeries_summable (f : ℕ → X → F) (A : ℝ)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j) (x : X) : Summable (fun j => f j x) :=
  (dyadic_summable.mul_left A).of_norm_bounded (fun j => hA j x)

lemma dyadicSeries_split_bound (f : ℕ → X → F) {A B : ℝ} (_hA₀ : 0≤A) (hB₀ : 0≤B)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j)
    (hB : ∀ j x y, ‖f j x-f j y‖≤B*4^j*dist x y) (x y : X) (N : ℕ) :
    ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ B*dist x y*4^N+4*A*((1:ℝ)/2)^N := by
  have hsx := dyadicSeries_summable f A hA x
  have hsy := dyadicSeries_summable f A hA y
  have hs := hsx.sub hsy
  rw [←hsx.tsum_sub hsy,←hs.sum_add_tsum_nat_add N]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      ‖∑ j ∈ range N, (f j x-f j y)‖ ≤ ∑ j ∈ range N, ‖f j x-f j y‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range N, B*4^j*dist x y := sum_le_sum (fun j _ => hB j x y)
      _ = B*dist x y*(∑ j ∈ range N, (4:ℝ)^j) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ B*dist x y*4^N := mul_le_mul_of_nonneg_left (four_pow_sum_le N) (mul_nonneg hB₀ dist_nonneg)
  · have htail : HasSum (fun j : ℕ => 2*A*(((1:ℝ)/2)^N)*((1:ℝ)/2)^j)
        (4*A*((1:ℝ)/2)^N) := by
      have h := dyadic_summable.hasSum.mul_left (2*A*((1:ℝ)/2)^N)
      rw [dyadic_tsum] at h
      have he : 2*A*((1:ℝ)/2)^N*2 = 4*A*((1:ℝ)/2)^N := by ring
      rw [he] at h
      exact h
    apply tsum_of_norm_bounded htail
    intro j
    calc
      ‖f (j+N) x-f (j+N) y‖ ≤ ‖f (j+N) x‖+‖f (j+N) y‖ := norm_sub_le _ _
      _ ≤ A*((1:ℝ)/2)^(j+N)+A*((1:ℝ)/2)^(j+N) := add_le_add (hA _ _) (hA _ _)
      _ = _ := by rw [pow_add]; ring

 
lemma dyadic_cubic_scale {d : ℝ} (hd : 0<d) (hd₁ : d≤1) :
    ∃ N : ℕ, d*4^N ≤ d^((1:ℝ)/3) ∧ ((1:ℝ)/2)^N ≤ 2*d^((1:ℝ)/3) := by
  let t : ℝ := d^((1:ℝ)/3)
  have ht : 0<t := Real.rpow_pos_of_pos hd _
  have ht₁ : t≤1 := Real.rpow_le_one hd.le hd₁ (by norm_num)
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one ht ht₁
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1:ℝ)/2<1)
  have hc : t^3=d := by
    dsimp [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul hd.le]
    norm_num
  have hn : (((1:ℝ)/2)^N)^2*4^N=1 := by
    rw [←pow_mul, Nat.mul_comm N 2, pow_mul, ←mul_pow]
    norm_num
  have hhi₂ : t^2 ≤ (((1:ℝ)/2)^N)^2 := pow_le_pow_left₀ ht.le hhi 2
  refine ⟨N,?_,?_⟩
  · have h : t^2*4^N≤1 := (mul_le_mul_of_nonneg_right hhi₂ (by positivity)).trans_eq hn
    calc
      d*4^N = t*(t^2*4^N) := by rw [←hc]; ring
      _ ≤ t*1 := mul_le_mul_of_nonneg_left h ht.le
      _ = _ := mul_one t
  · rw [pow_succ] at hlo
    change ((1:ℝ)/2)^N ≤ 2*t
    linarith

theorem dyadicSeries_holder (f : ℕ → X → F) {A B : ℝ} (hA₀ : 0≤A) (hB₀ : 0≤B)
    (hA : ∀ j x, ‖f j x‖≤A*((1:ℝ)/2)^j)
    (hB : ∀ j x y, ‖f j x-f j y‖≤B*4^j*dist x y) (x y : X) :
    ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ (B+8*A)*(dist x y)^((1:ℝ)/3) := by
  by_cases hzero : dist x y=0
  · have he : ∀ j, f j x=f j y := fun j => sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [hzero,mul_zero] using hB j x y) (norm_nonneg _)))
    simp only [he,sub_self,norm_zero]
    positivity
  have hd : 0<dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
  by_cases hd₁ : dist x y≤1
  · obtain ⟨N,hhead,htail⟩ := dyadic_cubic_scale hd hd₁
    apply (dyadicSeries_split_bound f hA₀ hB₀ hA hB x y N).trans
    have hh := mul_le_mul_of_nonneg_left hhead hB₀
    have ht := mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num : (0:ℝ)≤4) hA₀)
    nlinarith
  · have hsx := dyadicSeries_summable f A hA x
    have hsy := dyadicSeries_summable f A hA y
    have hb : ‖(∑' j, f j x)-(∑' j, f j y)‖ ≤ 4*A := by
      have hsum : HasSum (fun j : ℕ => A*((1:ℝ)/2)^j) (2*A) := by
        have h := dyadic_summable.hasSum.mul_left A
        rw [dyadic_tsum] at h
        have he : A*2 = 2*A := by ring
        rw [he] at h
        exact h
      exact (norm_sub_le _ _).trans ((add_le_add
        (tsum_of_norm_bounded hsum (fun j => hA j x))
        (tsum_of_norm_bounded hsum (fun j => hA j y))).trans_eq (by ring))
    have hr : 1≤(dist x y)^((1:ℝ)/3) := Real.one_le_rpow (le_of_not_ge hd₁) (by norm_num)
    exact hb.trans ((le_mul_of_one_le_right (by positivity) hr).trans
      (mul_le_mul_of_nonneg_right (by linarith : 4*A≤B+8*A) (Real.rpow_nonneg dist_nonneg _)))

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def dyadicKernelPotential (K : ℂ → ℂ) (g : ℂ → E) (x : ℂ) : E :=
  ∑' j : ℕ, scaledKernelPotential K (((1:ℝ)/8)^j) g x

def dyadicKernelDerivative (K : ℂ → ℂ) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∑' j : ℕ, scaledKernelDerivative K (((1:ℝ)/8)^j) g x

lemma dyadicKernel_value_summable {K : ℂ → ℂ} (hK : Continuous K)
    (hc : HasCompactSupport K) {g : ℂ → E} {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    Summable (fun j : ℕ => scaledKernelPotential K (((1:ℝ)/8)^j) g x) := by
  apply ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1:ℝ)/8‖ < 1)).mul_left
    ((∫ w : ℂ, ‖K w‖)*M)).of_norm_bounded
  intro j
  exact scaledKernel_value_bound hK hc (by positivity) hM x

lemma dyadicKernel_derivative_bound {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (j : ℕ) (x : ℂ) :
    ‖scaledKernelDerivative K (((1:ℝ)/8)^j) g x‖ ≤ (H*kernelMomentOne K)*((1:ℝ)/2)^j := by
  simpa only [eighth_rpow_third] using scaledKernel_derivative_bound hK hc (ε := ((1:ℝ)/8)^j) (by positivity) hg hH hHg x

lemma dyadicKernel_derivative_lipschitz {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (j : ℕ) (x y : ℂ) :
    ‖scaledKernelDerivative K (((1:ℝ)/8)^j) g x-scaledKernelDerivative K (((1:ℝ)/8)^j) g y‖ ≤
      (H*kernelMomentTwo K)*4^j*dist x y := by
  simpa only [eighth_scale_lipschitz,dist_eq_norm] using scaledKernel_derivative_lipschitz
    hK hc (ε := ((1:ℝ)/8)^j) (by positivity) hg hH hHg x y

theorem dyadicKernel_hasFDerivAt {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {M H : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    HasFDerivAt (dyadicKernelPotential K g) (dyadicKernelDerivative K g x) x := by
  apply hasFDerivAt_tsum (dyadic_summable.mul_left (H*kernelMomentOne K))
  · intro j x
    exact scaledKernel_hasFDerivAt hK hc (by positivity) hg x
  · exact dyadicKernel_derivative_bound hK hc hg hH hHg
  · exact dyadicKernel_value_summable hK.continuous hc hM (0:ℂ)

theorem dyadicKernel_derivative_holder {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ}
    (hH : 0 ≤ H) (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x y : ℂ) :
    ‖dyadicKernelDerivative K g x-dyadicKernelDerivative K g y‖ ≤
      (H*(kernelMomentTwo K+8*kernelMomentOne K))*‖x-y‖^((1:ℝ)/3) := by
  have h := dyadicSeries_holder (fun j => scaledKernelDerivative K (((1:ℝ)/8)^j) g)
    (mul_nonneg hH (kernelMomentOne_nonneg K)) (mul_nonneg hH (kernelMomentTwo_nonneg K))
    (dyadicKernel_derivative_bound hK hc hg hH hHg)
    (dyadicKernel_derivative_lipschitz hK hc hg hH hHg) x y
  rw [dist_eq_norm] at h
  exact h.trans_eq (by ring)

lemma dyadicKernel_derivative_continuous {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {H : ℝ}
    (hH : 0 ≤ H) (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    Continuous (dyadicKernelDerivative K g) := by
  have hsc (j : ℕ) : Continuous (scaledKernelDerivative K (((1:ℝ)/8)^j) g) := by
    have hge : Continuous (fun z : ℂ => g ((((1:ℝ)/8)^j) • z)) := by fun_prop
    have hs := hc.contDiff_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℂ)
      hK hge.locallyIntegrable
    exact (hs.continuous_fderiv (by simp)).comp (by fun_prop)
  exact continuous_tsum hsc (dyadic_summable.mul_left (H*kernelMomentOne K))
    (dyadicKernel_derivative_bound hK hc hg hH hHg)

theorem dyadicKernel_contDiff_one {K : ℂ → ℂ} (hK : ContDiff ℝ ∞ K)
    (hc : HasCompactSupport K) {g : ℂ → E} (hg : Continuous g) {M H : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (hH : 0 ≤ H)
    (hHg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) :
    ContDiff ℝ 1 (dyadicKernelPotential K g) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨dyadicKernelDerivative K g,dyadicKernel_derivative_continuous hK hc hg hH hHg,
    dyadicKernel_hasFDerivAt hK hc hg hM hH hHg⟩

end

open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def physicalScaledKernel (K : ℂ → ℂ) (ε : ℝ) (w : ℂ) : ℂ :=
  ε⁻¹ • K (ε⁻¹ • w)

omit [CompleteSpace E] in
lemma scaledKernel_asConvolution (K : ℂ → ℂ) {ε : ℝ} (hε : 0 < ε)
    (g : ℂ → E) (x : ℂ) :
    scaledKernelPotential K ε g x =
      MeasureTheory.convolution (physicalScaledKernel K ε) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  let f : ℂ → E := fun w => K w • g (x-ε • w)
  have hchange := Measure.integral_comp_inv_smul_of_nonneg volume f hε.le
  rw [Complex.finrank_real_complex] at hchange
  have hleft : scaledKernelPotential K ε g x = ε • ∫ w : ℂ, f w := by
    rw [scaledKernelPotential,MeasureTheory.convolution]
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro w
    simp only [f,ContinuousLinearMap.lsmul_apply,smul_sub,smul_smul,
      mul_inv_cancel₀ hε.ne',one_smul]
  have hright : MeasureTheory.convolution (physicalScaledKernel K ε) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x =
      ε⁻¹ • ∫ w : ℂ, f (ε⁻¹ • w) := by
    rw [MeasureTheory.convolution,←integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro w
    simp only [physicalScaledKernel,f,ContinuousLinearMap.lsmul_apply,smul_smul,
      mul_inv_cancel₀ hε.ne',one_smul,smul_assoc]
  rw [hleft,hright,hchange,smul_smul]
  congr 1
  field_simp

lemma physicalScaledKernel_integrable {K : ℂ → ℂ} (hK : Integrable K)
    {ε : ℝ} (hε : ε ≠ 0) : Integrable (physicalScaledKernel K ε) :=
  (hK.comp_smul (inv_ne_zero hε)).smul ε⁻¹

omit [CompleteSpace E] in
lemma scaledKernel_value_bound_integrable {K : ℂ → ℂ} (hK : Integrable K)
    {ε : ℝ} (hε : 0 ≤ ε) {g : ℂ → E}
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖scaledKernelPotential K ε g x‖ ≤ ((∫ w : ℂ, ‖K w‖)*M)*ε := by
  rw [scaledKernelPotential,norm_smul,Real.norm_of_nonneg hε]
  have hb : ‖MeasureTheory.convolution K (fun z => g (ε • z)) (ContinuousLinearMap.lsmul ℝ ℂ) volume (ε⁻¹ • x)‖ ≤
      (∫ w : ℂ, ‖K w‖)*M := by
    have hin : ∀ w : ℂ, ‖K w • g (ε • (ε⁻¹ • x-w))‖ ≤ ‖K w‖*M := by
      intro w
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    apply (norm_integral_le_of_norm_le (hK.norm.mul_const M)
      (Eventually.of_forall hin)).trans_eq
    exact integral_mul_const _ _
  exact (mul_le_mul_of_nonneg_left hb hε).trans_eq (by ring)

lemma locallyIntegrable_complex_inv_series : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact ae_of_all _ fun z => by simp only [norm_inv,Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_inv.aestronglyMeasurable

def cutoffCauchyKernel (b : ContDiffBump (0:ℂ)) (w : ℂ) : ℂ := b w • w⁻¹

lemma cutoffCauchyKernel_integrableNecessity (b : ContDiffBump (0:ℂ)) : Integrable (cutoffCauchyKernel b) := by
  have hi := locallyIntegrable_complex_inv_series.integrable_smul_left_of_hasCompactSupport
    b.continuous b.hasCompactSupport
  exact hi

lemma physicalScaled_cutoff (b : ContDiffBump (0:ℂ)) {ε : ℝ} (hε : ε ≠ 0) (w : ℂ) :
    physicalScaledKernel (cutoffCauchyKernel b) ε w = b (ε⁻¹ • w) • w⁻¹ := by
  change ε⁻¹ • (b (ε⁻¹ • w) • (ε⁻¹ • w)⁻¹) = _
  rw [smul_comm]
  congr 1
  simp [Complex.real_smul,mul_inv_rev,mul_left_comm,hε]

lemma physicalScaled_annular (b : ContDiffBump (0:ℂ)) (j : ℕ) (w : ℂ) :
    physicalScaledKernel (annularCauchyKernel b) (((1:ℝ)/8)^j) w =
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^j) w-
      physicalScaledKernel (cutoffCauchyKernel b) (((1:ℝ)/8)^(j+1)) w := by
  rw [physicalScaled_cutoff b (by positivity),physicalScaled_cutoff b (by positivity),←sub_smul]
  change (((1:ℝ)/8)^j)⁻¹ •
    ((b ((((1:ℝ)/8)^j)⁻¹ • w)-b ((8:ℝ) • ((((1:ℝ)/8)^j)⁻¹ • w))) •
      ((((1:ℝ)/8)^j)⁻¹ • w)⁻¹) = _
  rw [smul_comm]
  have hh : (((1:ℝ)/8)^j)⁻¹ • (((((1:ℝ)/8)^j)⁻¹ • w)⁻¹) = w⁻¹ := by
    simp [Complex.real_smul,mul_inv_rev,mul_left_comm]
  rw [hh]
  congr 2
  rw [pow_succ,mul_inv_rev,smul_smul]
  norm_num

end HigherDimensionalBallPacking.Rigidity

end

end OAI
