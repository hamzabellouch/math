import Mathlib
import OAI.Probability.ParisiFinite.AbsMulExpLe

namespace OAI

/-! Spin Trace. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
open SKGaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 
def spinTrace (β : ℝ) (x : ι → ℝ) : ℝ := logPartition (fun i => β*x i) / β

def gibbsMean (β : ℝ) (x v : ι → ℝ) : ℝ := ∑ i, weight (fun j => β*x j) i*v i

def gibbsCov (β : ℝ) (x v w : ι → ℝ) : ℝ :=
  gibbsMean β x (fun i => v i*w i)-gibbsMean β x v*gibbsMean β x w

lemma continuous_gibbsMean (β : ℝ) (v : ι → ℝ) : Continuous (fun x => gibbsMean β x v) := by
  unfold gibbsMean
  apply continuous_finsetSum
  intro i _
  exact ((continuous_weight i).comp (show Continuous (fun x : ι → ℝ => fun j => β*x j) by fun_prop)).mul_const _

lemma continuous_gibbsCov (β : ℝ) (v w : ι → ℝ) : Continuous (fun x => gibbsCov β x v w) :=
  (continuous_gibbsMean β _).sub ((continuous_gibbsMean β v).mul (continuous_gibbsMean β w))

lemma abs_gibbsMean_le (β : ℝ) (x v : ι → ℝ) : |gibbsMean β x v| ≤ ‖v‖ :=
  abs_weight_sum_le _ v (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)

lemma abs_gibbsCov_le (β : ℝ) (x v w : ι → ℝ) : |gibbsCov β x v w| ≤ 2*‖v‖*‖w‖ := by
  have hp : |gibbsMean β x (fun i => v i*w i)| ≤ ‖v‖*‖w‖ := by
    apply abs_weight_sum_le
    intro i
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i) (abs_nonneg _) (norm_nonneg _)
  have hm := mul_le_mul (abs_gibbsMean_le β x v) (abs_gibbsMean_le β x w) (abs_nonneg _) (norm_nonneg _)
  have h := abs_sub_le (gibbsMean β x (fun i => v i*w i)) 0 (gibbsMean β x v*gibbsMean β x w)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul] at h
  unfold gibbsCov
  linarith

lemma hasDerivAt_spinTrace {β : ℝ} (hβ : β ≠ 0) (v x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => spinTrace β (x+u • v)) (gibbsMean β (x+t • v) v) t := by
  have h : ∀ i, HasDerivAt (fun u : ℝ => β*(x+u • v) i) (β*v i) t := by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, id_eq] using
      (((hasDerivAt_id t).mul_const (v i)).const_add (x i)).const_mul β
  have hd := (hasDerivAt_logPartition h).div_const β
  have he : (∑ i, weight (fun j => β*(x+t • v) j) i*(β*v i))/β =
      gibbsMean β (x+t • v) v := by
    unfold gibbsMean
    simp only [mul_left_comm _ β, ← Finset.mul_sum, mul_div_cancel_left₀ _ hβ]
  rw [he] at hd
  exact hd

lemma hasDerivAt_gibbsMean (β : ℝ) (v w x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => gibbsMean β (x+u • v) w)
      (β*gibbsCov β (x+t • v) v w) t := by
  have h : ∀ i, HasDerivAt (fun u : ℝ => β*(x+u • v) i) (β*v i) t := by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, id_eq] using
      (((hasDerivAt_id t).mul_const (v i)).const_add (x i)).const_mul β
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hasDerivAt_weight h i).mul_const (w i))
  convert hd using 1 <;> try rfl
  unfold gibbsCov gibbsMean
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib,
    mul_left_comm _ β, ← Finset.mul_sum]
  simp only [mul_assoc, ← Finset.mul_sum]
  have hc (i : ι) : weight (fun j => β*(x+t • v) j) i *
      ((∑ j, weight (fun k => β*(x+t • v) k) j*v j)*w i) =
      (∑ j, weight (fun k => β*(x+t • v) k) j*v j)*
      (weight (fun j => β*(x+t • v) j) i*w i) := by ring
  simp_rw [hc, ← Finset.mul_sum]

lemma spinTrace_lipschitz {β : ℝ} (hβ : β ≠ 0) : LipschitzWith 1 (spinTrace (ι:=ι) β) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  let F : ℝ → ℝ := fun t => spinTrace β (y+t • (x-y))
  have hLip : LipschitzWith ‖x-y‖₊ F := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_spinTrace hβ (x-y) y t).differentiableAt)
    intro t
    rw [(hasDerivAt_spinTrace hβ (x-y) y t).deriv]
    exact_mod_cast abs_gibbsMean_le β (y+t • (x-y)) (x-y)
  have h := hLip.norm_sub_le 1 0
  simpa [F] using h

 

def traceField (β : ℝ≥0) (hβ : 0 < β) : DirectionalField (ι → ℝ) where
  val := spinTrace β
  first v x := gibbsMean β x v
  second v w x := (β:ℝ)*gibbsCov β x v w
  lip := 1
  lipschitz := spinTrace_lipschitz (show (β:ℝ) ≠ 0 from ne_of_gt hβ)
  continuousFirst := continuous_gibbsMean β
  continuousSecond v w := (continuous_gibbsCov β v w).const_mul _
  hasFirst := hasDerivAt_spinTrace (show (β:ℝ) ≠ 0 from ne_of_gt hβ)
  hasSecond := hasDerivAt_gibbsMean β
  boundFirst v := ‖v‖₊
  boundSecond v w := 2*β*‖v‖₊*‖w‖₊
  normFirst := fun v x => abs_gibbsMean_le β x v
  normSecond v w x := by
    rw [abs_mul, abs_of_nonneg β.coe_nonneg]
    have h := mul_le_mul_of_nonneg_left (abs_gibbsCov_le β x v w) β.coe_nonneg
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm, mul_assoc, mul_left_comm] using h

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ambient_exp_bound {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f)
    (a : ℝ) {x c : E} {K H C : ℝ} (hf0 : |f 0| ≤ K) (hx : ‖x‖ ≤ H)
    (hc : ‖c‖ ≤ C) (z : ℝ) :
    Real.exp (a*f (x+z • c)) ≤
      Real.exp (|a| *(K+(L:ℝ)*H))*Real.exp ((|a| *(L:ℝ)*C)*|z|) := by
  have h := ambient_exp_near_le_radius hf a 0 c (by simpa using hx) z
  apply h.trans
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (add_le_add hf0 le_rfl) (abs_nonneg _)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) (abs_nonneg _)
  · positivity
  · positivity

 

lemma continuous_parameterMoment {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] {L : ℝ≥0}
    {f g : S → E → ℝ} {x c : S → E} {M : S → ℝ}
    (hf : ∀ s, LipschitzWith L (f s))
    (hfc : Continuous (fun q : S × E => f q.1 q.2))
    (hgc : Continuous (fun q : S × E => g q.1 q.2))
    (hx : Continuous x) (hc : Continuous c) (hMc : Continuous M)
    (hM : ∀ s y, |g s y| ≤ M s) (a : ℝ) :
    Continuous (fun s => ambientMoment a (c s) (f s) (g s) (x s)) := by
  have hf0 : Continuous (fun s => f s 0) := hfc.comp (continuous_id.prodMk continuous_const)
  have hg (s : S) : Continuous (g s) := hgc.comp (continuous_const.prodMk continuous_id)
  apply continuous_iff_continuousAt.mpr
  intro s₀
  let K := |f s₀ 0|+1
  let H := ‖x s₀‖+1
  let C := ‖c s₀‖+1
  let N := |M s₀|+1
  have hK : ∀ᶠ s in 𝓝 s₀, |f s 0| < K := hf0.abs.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hH : ∀ᶠ s in 𝓝 s₀, ‖x s‖ < H := hx.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hC : ∀ᶠ s in 𝓝 s₀, ‖c s‖ < C := hc.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hN : ∀ᶠ s in 𝓝 s₀, M s < N := hMc.continuousAt.eventually
    (gt_mem_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one _)))
  apply continuousAt_of_dominated
    (bound := fun z => (Real.exp (|a| *(K+(L:ℝ)*H))*Real.exp ((|a| *(L:ℝ)*C)*|z|))*N)
  · exact Eventually.of_forall fun s => (integrable_ambient_weight (hf s) (hg s) (hM s) a (c s) (x s)).aestronglyMeasurable
  · filter_upwards [hK,hH,hC,hN] with s hsK hsH hsC hsN
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (ambient_exp_bound (hf s) a hsK.le hsH.le hsC.le z)
        ((hM s _).trans hsN.le) (abs_nonneg _) (by positivity)
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z => by
      have hv : Continuous (fun s => f s (x s+z • c s)) :=
        hfc.comp (continuous_id.prodMk (hx.add (hc.const_smul z)))
      have hw : Continuous (fun s => g s (x s+z • c s)) :=
        hgc.comp (continuous_id.prodMk (hx.add (hc.const_smul z)))
      exact ((Real.continuous_exp.comp (hv.const_mul a)).mul hw).continuousAt

lemma continuous_parameterMass {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] {L : ℝ≥0}
    {f : S → E → ℝ} {x c : S → E} (hf : ∀ s, LipschitzWith L (f s))
    (hfc : Continuous (fun q : S × E => f q.1 q.2)) (hx : Continuous x) (hc : Continuous c)
    (a : ℝ) : Continuous (fun s => ambientMass a (c s) (f s) (x s)) := by
  have h := continuous_parameterMoment hf hfc (g := fun _ _ => 1) continuous_const hx hc
    (M := fun _ => 1) continuous_const (by intro _ _; norm_num) a
  simpa only [ambientMass, ambientMoment, mul_one] using h

lemma continuous_parameterTilt {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] {L : ℝ≥0}
    {f g : S → E → ℝ} {x c : S → E} {M : S → ℝ}
    (hf : ∀ s, LipschitzWith L (f s))
    (hfc : Continuous (fun q : S × E => f q.1 q.2))
    (hgc : Continuous (fun q : S × E => g q.1 q.2))
    (hx : Continuous x) (hc : Continuous c) (hMc : Continuous M)
    (hM : ∀ s y, |g s y| ≤ M s) (a : ℝ) :
    Continuous (fun s => ambientTilt a (c s) (f s) (g s) (x s)) :=
  (continuous_parameterMoment hf hfc hgc hx hc hMc hM a).div
    (continuous_parameterMass hf hfc hx hc a) (fun s => (ambientMass_pos (hf s) a (c s) (x s)).ne')

lemma continuous_parameterAverage {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] {L : ℝ≥0}
    {f : S → E → ℝ} {x c : S → E} (hf : ∀ s, LipschitzWith L (f s))
    (hfc : Continuous (fun q : S × E => f q.1 q.2)) (hx : Continuous x) (hc : Continuous c) :
    Continuous (fun s => ∫ z, f s (x s+z • c s) ∂gaussianReal 0 1) := by
  have hf0 : Continuous (fun s => f s 0) := hfc.comp (continuous_id.prodMk continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro s₀
  let K := |f s₀ 0|+1
  let H := ‖x s₀‖+1
  let C := ‖c s₀‖+1
  have hK : ∀ᶠ s in 𝓝 s₀, |f s 0| < K := hf0.abs.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hH : ∀ᶠ s in 𝓝 s₀, ‖x s‖ < H := hx.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hC : ∀ᶠ s in 𝓝 s₀, ‖c s‖ < C := hc.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  apply continuousAt_of_dominated (bound := fun z => K+(L:ℝ)*(H+|z| *C))
  · exact Eventually.of_forall fun s => (integrable_ambient (hf s) (x s) (c s)).aestronglyMeasurable
  · filter_upwards [hK,hH,hC] with s hsK hsH hsC
    exact ae_of_all _ fun z => by
      have hv := (hf s).norm_sub_le (x s+z • c s) 0
      have ht := norm_add_le (x s) (z • c s)
      rw [norm_smul, Real.norm_eq_abs] at ht
      simp only [sub_zero, Real.norm_eq_abs] at hv
      have htri := abs_add_le (f s (x s+z • c s)-f s 0) (f s 0)
      rw [sub_add_cancel] at htri
      rw [Real.norm_eq_abs]
      have hc' := mul_le_mul_of_nonneg_left hsC.le (abs_nonneg z)
      nlinarith [L.coe_nonneg]
  · exact (integrable_const _).add (((integrable_const _).add
      ((MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)).abs.mul_const _)).const_mul _)
  · exact ae_of_all _ fun z =>
      (hfc.comp (continuous_id.prodMk (hx.add (hc.const_smul z)))).continuousAt

lemma continuous_parameterStep {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] {L : ℝ≥0}
    {f : S → E → ℝ} {x c : S → E} (hf : ∀ s, LipschitzWith L (f s))
    (hfc : Continuous (fun q : S × E => f q.1 q.2)) (hx : Continuous x) (hc : Continuous c)
    (a : ℝ) : Continuous (fun s => ambientStep a (c s) (f s) (x s)) := by
  by_cases ha : a=0
  · subst a
    simpa [ambientStep, logMean] using continuous_parameterAverage hf hfc hx hc
  · have he : (fun s => ambientStep a (c s) (f s) (x s)) =
        fun s => Real.log (ambientMass a (c s) (f s) (x s))/a := by
      funext s
      simp [ambientStep, logMean, ha, ambientMass]
    rw [he]
    exact ((continuous_parameterMass hf hfc hx hc a).log
      (fun s => (ambientMass_pos (hf s) a (c s) (x s)).ne')).div_const a
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_parameterMass {L : ℝ≥0} {f d : ℝ → E → ℝ} {M : ℝ → ℝ}
    (hf : ∀ t, LipschitzWith L (f t))
    (hfc : Continuous (fun q : ℝ × E => f q.1 q.2))
    (hdc : Continuous (fun q : ℝ × E => d q.1 q.2))
    (hMc : Continuous M) (hM : ∀ t y, |d t y| ≤ M t)
    (hd : ∀ y t, HasDerivAt (fun s => f s y) (d t y) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientMass a c (f t) x)
      (a*ambientMoment a c (f t₀) (d t₀) x) t₀ := by
  let K := |f t₀ 0|+1
  let N := |M t₀|+1
  have hf0 : Continuous (fun t => f t 0) := hfc.comp (continuous_id.prodMk continuous_const)
  have hK : ∀ᶠ t in 𝓝 t₀, |f t 0| < K := hf0.abs.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  have hN : ∀ᶠ t in 𝓝 t₀, M t < N := hMc.continuousAt.eventually
    (gt_mem_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one _)))
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp (hK.and hN)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t₀ r) (μ := gaussianReal 0 1)
    (F := fun t z => Real.exp (a*f t (x+z • c)))
    (bound := fun z => (Real.exp (|a| *(K+(L:ℝ)*‖x‖))*
      Real.exp ((|a| *(L:ℝ)*‖c‖)*|z|))*(|a| *N))
    (F' := fun t z => Real.exp (a*f t (x+z • c))*(a*d t (x+z • c)))
    (Metric.ball_mem_nhds _ hr) ?_ (integrable_exp_ambient (hf t₀) a x c) ?_ ?_ ?_ ?_).2
  · convert h using 1 <;> try rfl
    simp only [ambientMoment, mul_left_comm _ a, integral_const_mul]
  · exact Eventually.of_forall fun t => (integrable_exp_ambient (hf t) a x c).aestronglyMeasurable
  · have hdc0 : Continuous (d t₀) := hdc.comp (continuous_const.prodMk continuous_id)
    have hfc0 := (hf t₀).continuous
    fun_prop
  · exact ae_of_all _ fun z t ht => by
      have hk := (hs ht).1.le
      have hn := (hs ht).2.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
      apply mul_le_mul (ambient_exp_bound (hf t) a hk le_rfl le_rfl z)
      · exact mul_le_mul_of_nonneg_left ((hM t _).trans hn) (abs_nonneg _)
      · positivity
      · positivity
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z t _ => by
      convert ((hd (x+z • c) t).const_mul a).exp using 1

lemma hasDerivAt_parameterAverage {L : ℝ≥0} {f d : ℝ → E → ℝ} {M : ℝ → ℝ}
    (hf : ∀ t, LipschitzWith L (f t))
    (hdc : Continuous (fun q : ℝ × E => d q.1 q.2))
    (hMc : Continuous M) (hM : ∀ t y, |d t y| ≤ M t)
    (hd : ∀ y t, HasDerivAt (fun s => f s y) (d t y) t)
    (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z, f t (x+z • c) ∂gaussianReal 0 1)
      (∫ z, d t₀ (x+z • c) ∂gaussianReal 0 1) t₀ := by
  let N := |M t₀|+1
  have hN : ∀ᶠ t in 𝓝 t₀, M t < N := hMc.continuousAt.eventually
    (gt_mem_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one _)))
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hN
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t₀ r) (bound := fun _ => N) (F' := fun t z => d t (x+z • c))
    (Metric.ball_mem_nhds _ hr) ?_ (integrable_ambient (hf t₀) x c) ?_ ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall fun t => (integrable_ambient (hf t) x c).aestronglyMeasurable
  · have hdc0 : Continuous (d t₀) := hdc.comp (continuous_const.prodMk continuous_id)
    fun_prop
  · exact ae_of_all _ fun z t ht => by
      rw [Real.norm_eq_abs]
      exact (hM t _).trans (hs ht).le
  · exact ae_of_all _ fun z t _ => hd _ t

 

lemma hasDerivAt_parameterStep {L : ℝ≥0} {f d : ℝ → E → ℝ} {M : ℝ → ℝ}
    (hf : ∀ t, LipschitzWith L (f t))
    (hfc : Continuous (fun q : ℝ × E => f q.1 q.2))
    (hdc : Continuous (fun q : ℝ × E => d q.1 q.2))
    (hMc : Continuous M) (hM : ∀ t y, |d t y| ≤ M t)
    (hd : ∀ y t, HasDerivAt (fun s => f s y) (d t y) t)
    (a : ℝ) (c x : E) (t₀ : ℝ) :
    HasDerivAt (fun t => ambientStep a c (f t) x)
      (ambientTilt a c (f t₀) (d t₀) x) t₀ := by
  by_cases ha : a=0
  · subst a
    simpa [ambientStep, logMean] using
      hasDerivAt_parameterAverage hf hdc hMc hM hd c x t₀
  · have h := ((hasDerivAt_parameterMass hf hfc hdc hMc hM hd a c x t₀).log
      (ambientMass_pos (hf t₀) a c x).ne').div_const a
    have hv : (fun t => ambientStep a c (f t) x) = fun t => Real.log (ambientMass a c (f t) x)/a := by
      funext t
      simp [ambientStep, logMean, ha, ambientMass]
    rw [hv]
    convert h using 1
    try rfl
    unfold ambientTilt
    field_simp
end ParisiFinite

 

open Filter
open scoped Topology
namespace ParisiFinite

lemma hasDerivAt_bivariate_path {f d₁ d₂ : ℝ → ℝ → ℝ}
    (hd₁ : ∀ t s, HasDerivAt (fun r => f r s) (d₁ t s) t)
    (hd₂ : ∀ t s, HasDerivAt (f t) (d₂ t s) s)
    (hc₁ : Continuous (fun p : ℝ × ℝ => d₁ p.1 p.2))
    (hc₂ : Continuous (fun p : ℝ × ℝ => d₂ p.1 p.2))
    {s : ℝ → ℝ} {ds t₀ : ℝ} (hs : HasDerivAt s ds t₀) :
    HasDerivAt (fun t => f t (s t)) (d₁ t₀ (s t₀)+ds*d₂ t₀ (s t₀)) t₀ := by
  have h := hasStrictFDerivAt_uncurry_coprod
    (f := f) (u := (t₀,s t₀))
    (f₁ := fun t s => ContinuousLinearMap.toSpanSingleton ℝ (d₁ t s))
    (f₂ := fun t s => ContinuousLinearMap.toSpanSingleton ℝ (d₂ t s))
    (Eventually.of_forall fun p => (hd₁ p.1 p.2).hasFDerivAt)
    (Eventually.of_forall fun p => (hd₂ p.1 p.2).hasFDerivAt)
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hc₁).continuousAt)
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hc₂).continuousAt)
  have hv := h.hasFDerivAt.comp_hasDerivAt t₀ ((hasDerivAt_id t₀).prodMk hs)
  convert hv using 1 <;> try rfl
  change d₁ t₀ (s t₀)+ds*d₂ t₀ (s t₀) = 1*d₁ t₀ (s t₀)+ds*d₂ t₀ (s t₀)
  ring

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

 

structure FieldFamily (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  field : ℝ → DirectionalField E
  dot : ℝ → E → ℝ
  continuousVal : Continuous (fun q : ℝ × E => (field q.1).val q.2)
  continuousFirst : ∀ v, Continuous (fun q : ℝ × E => (field q.1).first v q.2)
  continuousSecond : ∀ v w, Continuous (fun q : ℝ × E => (field q.1).second v w q.2)
  continuousDot : Continuous (fun q : ℝ × E => dot q.1 q.2)
  hasDot : ∀ x t, HasDerivAt (fun s => (field s).val x) (dot t x) t
  lip : ℝ≥0
  lipschitz : ∀ t, LipschitzWith lip (field t).val
  boundFirst : E → ℝ≥0
  boundSecond : E → E → ℝ≥0
  boundDot : ℝ → ℝ
  continuousBound : Continuous boundDot
  normFirst : ∀ t v x, |(field t).first v x| ≤ boundFirst v
  normSecond : ∀ t v w x, |(field t).second v w x| ≤ boundSecond v w
  normDot : ∀ t x, |dot t x| ≤ boundDot t

namespace FieldFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma square_bound {g : E → ℝ} {B : ℝ≥0} (h : ∀ y, |g y| ≤ B) (x : E) :
    |g x ^ 2| ≤ (B:ℝ)^2 := by
  rw [abs_sq]
  nlinarith [h x, abs_nonneg (g x), sq_abs (g x)]

def constant (f : DirectionalField E) : FieldFamily E where
  field _ := f
  dot _ _ := 0
  continuousVal := f.lipschitz.continuous.comp continuous_snd
  continuousFirst v := (f.continuousFirst v).comp continuous_snd
  continuousSecond v w := (f.continuousSecond v w).comp continuous_snd
  continuousDot := continuous_const
  hasDot x t := hasDerivAt_const t (f.val x)
  lip := f.lip
  lipschitz _ := f.lipschitz
  boundFirst := f.boundFirst
  boundSecond := f.boundSecond
  boundDot _ := 0
  continuousBound := continuous_const
  normFirst _ := f.normFirst
  normSecond _ := f.normSecond
  normDot _ _ := by simp

lemma continuous_mapTilt (F : FieldFamily E) {S : Type*} [TopologicalSpace S]
    [FirstCountableTopology S] {t : S → ℝ} {x c : S → E} {g : ℝ → E → ℝ} {M : ℝ → ℝ}
    (ht : Continuous t) (hx : Continuous x) (hc : Continuous c)
    (hg : Continuous (fun q : ℝ × E => g q.1 q.2)) (hMc : Continuous M)
    (hM : ∀ u y, |g u y| ≤ M u) (a : ℝ) :
    Continuous (fun p => ambientTilt a (c p) (F.field (t p)).val (g (t p)) (x p)) := by
  apply continuous_parameterTilt (fun p => F.lipschitz (t p))
    (F.continuousVal.comp ((ht.comp continuous_fst).prodMk continuous_snd))
    (hg.comp ((ht.comp continuous_fst).prodMk continuous_snd)) hx hc (hMc.comp ht)
    (fun p y => hM (t p) y) a

lemma continuous_mapStep (F : FieldFamily E) {S : Type*} [TopologicalSpace S]
    [FirstCountableTopology S] {t : S → ℝ} {x c : S → E}
    (ht : Continuous t) (hx : Continuous x) (hc : Continuous c) (a : ℝ) :
    Continuous (fun p => ambientStep a (c p) (F.field (t p)).val (x p)) :=
  continuous_parameterStep (fun p => F.lipschitz (t p))
    (F.continuousVal.comp ((ht.comp continuous_fst).prodMk continuous_snd)) hx hc a

 

def transformedDot (F : FieldFamily E) (a : ℝ≥0) (c : E) (s ds : ℝ → ℝ) (t : ℝ) (x : E) : ℝ :=
  ambientTilt a (s t • c) (F.field t).val (F.dot t) x + s t*ds t *
    (ambientTilt a (s t • c) (F.field t).val ((F.field t).second c c) x + (a:ℝ)*
      ambientTilt a (s t • c) (F.field t).val (fun y => ((F.field t).first c y)^2) x)

lemma hasDerivAt_transformed (F : FieldFamily E) (a : ℝ≥0) (c x : E)
    {s ds : ℝ → ℝ} (_hc : Continuous s) (hd : ∀ t, HasDerivAt s (ds t) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ((F.field t).transform a (s t • c)).val x)
      (F.transformedDot a c s ds t₀ x) t₀ := by
  let D₁ (t r : ℝ) := ambientTilt a (r • c) (F.field t).val (F.dot t) x
  let D₂ (t r : ℝ) := r*(ambientTilt a (r • c) (F.field t).val ((F.field t).second c c) x+
    (a:ℝ)*ambientTilt a (r • c) (F.field t).val (fun y => ((F.field t).first c y)^2) x)
  have h₁ : Continuous (fun p : ℝ × ℝ => D₁ p.1 p.2) :=
    F.continuous_mapTilt continuous_fst continuous_const (continuous_snd.smul continuous_const)
      F.continuousDot F.continuousBound F.normDot a
  have h₂a : Continuous (fun p : ℝ × ℝ =>
      ambientTilt a (p.2 • c) (F.field p.1).val ((F.field p.1).second c c) x) :=
    F.continuous_mapTilt continuous_fst continuous_const (continuous_snd.smul continuous_const)
      (F.continuousSecond c c) continuous_const (fun t y => F.normSecond t c c y) a
  have h₂b : Continuous (fun p : ℝ × ℝ =>
      ambientTilt a (p.2 • c) (F.field p.1).val (fun y => ((F.field p.1).first c y)^2) x) :=
    F.continuous_mapTilt continuous_fst continuous_const (continuous_snd.smul continuous_const)
      ((F.continuousFirst c).pow 2) continuous_const
      (fun t y => square_bound (fun z => F.normFirst t c z) y) a
  have h₂ : Continuous (fun p : ℝ × ℝ => D₂ p.1 p.2) :=
    continuous_snd.mul (h₂a.add (h₂b.const_mul _))
  have h := hasDerivAt_bivariate_path
    (fun t r => hasDerivAt_parameterStep F.lipschitz F.continuousVal F.continuousDot
      F.continuousBound F.normDot F.hasDot a (r • c) x t)
    (fun t r => (F.field t).hasDerivAt_transform_scale a c x r) h₁ h₂ (hd t₀)
  convert h using 1 <;> first | rfl | simp only [transformedDot]; ring
end FieldFamily
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite.FieldFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_transformedDot (F : FieldFamily E) (a : ℝ≥0) (c : E)
    {s ds : ℝ → ℝ} (hs : Continuous s) (hds : Continuous ds) :
    Continuous (fun q : ℝ × E => F.transformedDot a c s ds q.1 q.2) := by
  have hc : Continuous (fun q : ℝ × E => s q.1 • c) := (hs.comp continuous_fst).smul continuous_const
  have h1 := F.continuous_mapTilt continuous_fst continuous_snd hc
    F.continuousDot F.continuousBound F.normDot a
  have h2 := F.continuous_mapTilt continuous_fst continuous_snd hc
    (F.continuousSecond c c) continuous_const (fun t y => F.normSecond t c c y) a
  have h3 := F.continuous_mapTilt continuous_fst continuous_snd hc
    ((F.continuousFirst c).pow 2) continuous_const
    (fun t y => square_bound (fun z => F.normFirst t c z) y) a
  exact h1.add (((hs.comp continuous_fst).mul (hds.comp continuous_fst)).mul (h2.add (h3.const_mul _)))

lemma bound_transformedDot (F : FieldFamily E) (a : ℝ≥0) (c : E) (s ds : ℝ → ℝ) (t : ℝ) (x : E) :
    |F.transformedDot a c s ds t x| ≤ F.boundDot t + |s t*ds t| *
      ((F.boundSecond c c:ℝ)+(a:ℝ)*(F.boundFirst c:ℝ)^2) := by
  have h1 := abs_ambientTilt_le (F.lipschitz t)
    (F.continuousDot.comp (continuous_const.prodMk continuous_id)) (F.normDot t) (a:ℝ) (s t • c) x
  have hsec := abs_ambientTilt_le (F.lipschitz t) ((F.field t).continuousSecond c c)
    (F.normSecond t c c) (a:ℝ) (s t • c) x
  have hsq := abs_ambientTilt_le (F.lipschitz t) (((F.field t).continuousFirst c).pow 2)
    (fun y => square_bound (fun z => F.normFirst t c z) y) (a:ℝ) (s t • c) x
  unfold transformedDot
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  apply add_le_add h1
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg a.coe_nonneg]
  exact add_le_add hsec (mul_le_mul_of_nonneg_left hsq a.coe_nonneg)

 

def transform (F : FieldFamily E) (a : ℝ≥0) (c : E) (s ds : ℝ → ℝ)
    (hs : Continuous s) (hds : Continuous ds) (hd : ∀ t, HasDerivAt s (ds t) t) : FieldFamily E where
  field t := (F.field t).transform a (s t • c)
  dot := F.transformedDot a c s ds
  continuousVal := F.continuous_mapStep continuous_fst continuous_snd
    ((hs.comp continuous_fst).smul continuous_const) a
  continuousFirst v := F.continuous_mapTilt continuous_fst continuous_snd
    ((hs.comp continuous_fst).smul continuous_const) (F.continuousFirst v) continuous_const
    (fun t y => F.normFirst t v y) a
  continuousSecond v w := by
    have hc : Continuous (fun q : ℝ × E => s q.1 • c) := (hs.comp continuous_fst).smul continuous_const
    have h1 := F.continuous_mapTilt continuous_fst continuous_snd hc
      (F.continuousFirst v) continuous_const (fun t y => F.normFirst t v y) a
    have h2 := F.continuous_mapTilt continuous_fst continuous_snd hc
      (F.continuousFirst w) continuous_const (fun t y => F.normFirst t w y) a
    have h12 := F.continuous_mapTilt continuous_fst continuous_snd hc
      (F.continuousSecond v w) continuous_const (fun t y => F.normSecond t v w y) a
    have hp := F.continuous_mapTilt
      (g := fun t y => (F.field t).first v y * (F.field t).first w y)
      (M := fun _ => (F.boundFirst v:ℝ)*(F.boundFirst w:ℝ))
      continuous_fst continuous_snd hc
      ((F.continuousFirst v).mul (F.continuousFirst w)) continuous_const
      (fun t y => by
        rw [abs_mul]
        exact mul_le_mul (F.normFirst t v y) (F.normFirst t w y) (abs_nonneg _) (F.boundFirst v).coe_nonneg) a
    exact h12.add ((hp.sub (h1.mul h2)).const_mul _)
  continuousDot := F.continuous_transformedDot a c hs hds
  hasDot x t := F.hasDerivAt_transformed a c x hs hd t
  lip := F.lip
  lipschitz t := ambientStep_lipschitz (F.lipschitz t) a.coe_nonneg (s t • c)
  boundFirst := F.boundFirst
  boundSecond v w := F.boundSecond v w + 2*a*F.boundFirst v*F.boundFirst w
  boundDot t := F.boundDot t + |s t*ds t| *((F.boundSecond c c:ℝ)+(a:ℝ)*(F.boundFirst c:ℝ)^2)
  continuousBound := F.continuousBound.add (((hs.mul hds).abs).mul_const _)
  normFirst t v x := abs_ambientTilt_le (F.lipschitz t) ((F.field t).continuousFirst v)
    (F.normFirst t v) a (s t • c) x
  normSecond t v w x := by
    have h1 := abs_ambientTilt_le (F.lipschitz t) ((F.field t).continuousFirst v) (F.normFirst t v) (a:ℝ) (s t • c) x
    have h2 := abs_ambientTilt_le (F.lipschitz t) ((F.field t).continuousFirst w) (F.normFirst t w) (a:ℝ) (s t • c) x
    have h12 := abs_ambientTilt_le (F.lipschitz t) ((F.field t).continuousSecond v w) (F.normSecond t v w) (a:ℝ) (s t • c) x
    have hp := abs_ambientTilt_le (F.lipschitz t) (((F.field t).continuousFirst v).mul ((F.field t).continuousFirst w))
      (fun y => by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul (F.normFirst t v y) (F.normFirst t w y) (abs_nonneg _) (F.boundFirst v).coe_nonneg) (a:ℝ) (s t • c) x
    change |ambientTilt a (s t • c) (F.field t).val (fun y => (F.field t).first v y * (F.field t).first w y) x| ≤
      (F.boundFirst v:ℝ)*(F.boundFirst w:ℝ) at hp
    have hprod := mul_le_mul h1 h2 (abs_nonneg _) (F.boundFirst v).coe_nonneg
    have hsub := abs_sub_le
      (ambientTilt a (s t • c) (F.field t).val (fun y => (F.field t).first v y*(F.field t).first w y) x) 0
      (ambientTilt a (s t • c) (F.field t).val ((F.field t).first v) x *
        ambientTilt a (s t • c) (F.field t).val ((F.field t).first w) x)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul] at hsub
    change |ambientTilt a (s t • c) (F.field t).val ((F.field t).second v w) x + (a:ℝ)*
      (ambientTilt a (s t • c) (F.field t).val (fun y => (F.field t).first v y*(F.field t).first w y) x -
        ambientTilt a (s t • c) (F.field t).val ((F.field t).first v) x *
        ambientTilt a (s t • c) (F.field t).val ((F.field t).first w) x)| ≤ _
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg a.coe_nonneg]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [a.coe_nonneg]
  normDot := F.bound_transformedDot a c s ds
end ParisiFinite.FieldFamily

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

 

structure MovingCoordinate (E : Type*) where
  gamma : ℝ≥0
  direction : E
  scale : ℝ → ℝ
  velocity : ℝ → ℝ
  continuousScale : Continuous scale
  continuousVelocity : Continuous velocity
  hasScale : ∀ t, HasDerivAt scale (velocity t) t

namespace MovingCoordinate
variable {E : Type*}

def sine (a : ℝ≥0) (c : E) : MovingCoordinate E where
  gamma := a
  direction := c
  scale := Real.sin
  velocity := Real.cos
  continuousScale := Real.continuous_sin
  continuousVelocity := Real.continuous_cos
  hasScale := Real.hasDerivAt_sin

def cosine (a : ℝ≥0) (c : E) : MovingCoordinate E where
  gamma := a
  direction := c
  scale := Real.cos
  velocity t := -Real.sin t
  continuousScale := Real.continuous_cos
  continuousVelocity := Real.continuous_sin.neg
  hasScale := Real.hasDerivAt_cos

def constant (a : ℝ≥0) (c : E) (s : ℝ) : MovingCoordinate E where
  gamma := a
  direction := c
  scale _ := s
  velocity _ := 0
  continuousScale := continuous_const
  continuousVelocity := continuous_const
  hasScale t := hasDerivAt_const t s
end MovingCoordinate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

def hierarchy (f : DirectionalField E) : List (MovingCoordinate E) → FieldFamily E
  | [] => FieldFamily.constant f
  | c::cs => (hierarchy f cs).transform c.gamma c.direction c.scale c.velocity
      c.continuousScale c.continuousVelocity c.hasScale

def hierarchyValue (f : E → ℝ) : List (MovingCoordinate E) → ℝ → E → ℝ
  | [] => fun _ => f
  | c::cs => fun t => ambientStep c.gamma (c.scale t • c.direction) (hierarchyValue f cs t)

lemma hierarchy_val (f : DirectionalField E) (cs : List (MovingCoordinate E)) (t : ℝ) :
    ((hierarchy f cs).field t).val = hierarchyValue f.val cs t := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ambientStep c.gamma (c.scale t • c.direction) ((hierarchy f cs).field t).val = _
    rw [ih]
    rfl

 

lemma hasDerivAt_hierarchyValue (f : DirectionalField E) (cs : List (MovingCoordinate E)) (t : ℝ) (x : E) :
    HasDerivAt (fun s => hierarchyValue f.val cs s x) ((hierarchy f cs).dot t x) t := by
  have h := (hierarchy f cs).hasDot x t
  simpa only [hierarchy_val] using h

lemma hierarchy_dot_cons (f : DirectionalField E) (c : MovingCoordinate E)
    (cs : List (MovingCoordinate E)) (t : ℝ) (x : E) :
    (hierarchy f (c::cs)).dot t x =
      ambientTilt c.gamma (c.scale t • c.direction) ((hierarchy f cs).field t).val
        ((hierarchy f cs).dot t) x + c.scale t*c.velocity t *
      (ambientTilt c.gamma (c.scale t • c.direction) ((hierarchy f cs).field t).val
        (((hierarchy f cs).field t).second c.direction c.direction) x + (c.gamma:ℝ)*
      ambientTilt c.gamma (c.scale t • c.direction) ((hierarchy f cs).field t).val
        (fun y => (((hierarchy f cs).field t).first c.direction y)^2) x) := rfl

lemma ambientStep_zero_direction (a : ℝ) (f : E → ℝ) (x : E) : ambientStep a 0 f x = f x := by
  by_cases ha : a=0
  · simp [ambientStep, logMean, ha]
  · simp [ambientStep, logMean, ha, Real.log_exp]

lemma hierarchyValue_zero_scales (f : E → ℝ) (cs : List (MovingCoordinate E)) (t : ℝ)
    (ht : ∀ c ∈ cs, c.scale t = 0) : hierarchyValue f cs t = f := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := ht c (by simp)
    have hcs : ∀ d ∈ cs, d.scale t = 0 := fun d hd => ht d (by simp [hd])
    simp only [hierarchyValue, hc, zero_smul, ih hcs]
    funext x
    exact ambientStep_zero_direction c.gamma f x
end ParisiFinite

end

end OAI
