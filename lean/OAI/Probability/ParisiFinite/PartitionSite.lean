import Mathlib
import OAI.Probability.ParisiFinite.LogMean

namespace OAI

/-! Partition Site. -/

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace ParisiInterpolation
open SKGaussian SKQAOA ParisiFinite

lemma partition_site (n : ℕ) (a : Fin n → ℝ) :
    partition (fun σ : Configuration n => ∑ i, a i * spin σ i) =
      ∏ i, (2 * Real.cosh (a i)) := by
  classical
  unfold partition spin
  simp_rw [Real.exp_sum]
  rw [← Fintype.prod_sum (fun i (b : Bool) => Real.exp (a i * (if b then -1 else 1)))]
  apply Finset.prod_congr rfl
  intro i _
  simp [Real.cosh_eq]
  ring

lemma logPartition_site (n : ℕ) (a : Fin n → ℝ) :
    logPartition (fun σ : Configuration n => ∑ i, a i * spin σ i) =
      ∑ i, Real.log (2 * Real.cosh (a i)) := by
  rw [logPartition, partition_site]
  exact Real.log_prod (fun _ _ => (mul_pos (by norm_num) (Real.cosh_pos _)).ne')

lemma siteCoeff_field (n : ℕ) (β q : ℝ) (x : Fin n → ℝ) :
    field (siteCoeff n β q) x = fun σ : Configuration n => ∑ i, (β * (Real.sqrt q * x i)) * spin σ i := by
  funext σ
  apply Finset.sum_congr rfl
  intro i _
  dsimp [siteCoeff]
  ring

lemma logPartition_siteCoeff (n : ℕ) (β q : ℝ) (x : Fin n → ℝ) :
    logPartition (field (siteCoeff n β q) x) =
      ∑ i, Real.log (2 * Real.cosh (β * (Real.sqrt q * x i))) := by
  rw [siteCoeff_field, logPartition_site]

lemma log_cosh_integrable {β : ℝ} (hβ : 0 < β) (s : ℝ) :
    Integrable (fun z => Real.log (2 * Real.cosh (β * (s * z)))) (gaussianReal 0 1) := by
  have h := (integrable_shift (terminal_lipschitz hβ) 0 s).const_mul β
  have he (z : ℝ) : β * terminal β (0 + s * z) = Real.log (2 * Real.cosh (β * (s * z))) := by
    simp only [terminal, zero_add]
    field_simp
  simpa only [he] using h

lemma expected_siteCoeff (n : ℕ) {β : ℝ} (hβ : 0 < β) (q : ℝ) :
    expected (siteCoeff n β q) =
      (n : ℝ) * ∫ z : ℝ, Real.log (2 * Real.cosh (β * (Real.sqrt q * z))) ∂gaussianReal 0 1 := by
  have hi (i : Fin n) : Integrable (fun x : Fin n → ℝ =>
      Real.log (2 * Real.cosh (β * (Real.sqrt q * x i)))) (gaussianLaw (Fin n)) :=
    ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp
      (log_cosh_integrable hβ (Real.sqrt q)).aestronglyMeasurable).mpr
        (log_cosh_integrable hβ (Real.sqrt q))
  unfold expected
  simp_rw [logPartition_siteCoeff]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin n) : (∫ x : Fin n → ℝ,
      Real.log (2 * Real.cosh (β * (Real.sqrt q * x i))) ∂gaussianLaw (Fin n)) =
      ∫ z : ℝ, Real.log (2 * Real.cosh (β * (Real.sqrt q * z))) ∂gaussianReal 0 1 := by
    have hm := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
    rw [← hm.map_eq]
    exact (integral_map hm.measurable.aemeasurable
      (hm.map_eq.symm ▸ (log_cosh_integrable hβ (Real.sqrt q)).aestronglyMeasurable)).symm
  simp_rw [he]
  simp

lemma interpolatedPressure_zero (n : ℕ) {β : ℝ} (hβ : 0 < β) (q : ℝ) :
    interpolatedPressure n β q 0 =
      (n : ℝ) * ∫ z : ℝ, Real.log (2 * Real.cosh (β * (Real.sqrt q * z))) ∂gaussianReal 0 1 := by
  unfold interpolatedPressure
  have he : rotate (siteLift n β q) (skLift n β) 0 = siteLift n β q := by
    funext σ k
    simp [rotate]
  rw [he]
  unfold expected siteLift
  rw [integral_field_inl]
  exact expected_siteCoeff n hβ q

lemma interpolatedPressure_pi_div_two (n : ℕ) (β q : ℝ) :
    interpolatedPressure n β q (Real.pi / 2) = pressure β n := by
  unfold interpolatedPressure
  have he : rotate (siteLift n β q) (skLift n β) (Real.pi / 2) = skLift n β := by
    funext σ k
    simp [rotate]
  rw [he]
  unfold expected skLift
  rw [integral_field_inr]
  simp_rw [field_scale, field_skCoeff]
  rfl

end ParisiInterpolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace ParisiInterpolation
open SKGaussian SKQAOA ParisiFinite

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

lemma norm_replicaAverage_le (A : ι → κ → ℝ) (K : ι → ι → ℝ) (x : κ → ℝ) :
    ‖replicaAverage A K x‖ ≤ ∑ i, ∑ j, |K i j| := by
  unfold replicaAverage
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)]
  exact mul_le_of_le_one_left (abs_nonneg _)
    ((mul_le_of_le_one_left (weight_pos _ _).le (weight_le_one _ _)).trans
      (weight_le_one _ _))

lemma continuous_replicaMean_rotate (A B : ι → κ → ℝ) (K : ι → ι → ℝ) :
    Continuous (fun t => replicaMean (rotate A B t) K) := by
  apply continuous_of_dominated
    (fun t => (integrable_replicaAverage (rotate A B t) K).aestronglyMeasurable)
    (fun t => ae_of_all _ (norm_replicaAverage_le (rotate A B t) K))
    (integrable_const _)
  exact ae_of_all _ fun x => by
    unfold replicaAverage
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    have hf : Continuous (fun t => field (rotate A B t) x) := by
      unfold field rotate
      fun_prop
    exact (((continuous_weight i).comp hf).mul ((continuous_weight j).comp hf)).mul_const _

lemma continuous_remainder (n : ℕ) (β q : ℝ) : Continuous (remainder n β q) :=
  continuous_replicaMean_rotate _ _ _

 

lemma hasDerivAt_correctedPressure {n : ℕ} (hn : 0 < n) (β : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (t : ℝ) :
    HasDerivAt (fun s => interpolatedPressure n β q s -
        β^2 * n / 4 * (Real.sin s)^2 * (1-q)^2)
      (-(β^2 * n / 2) * (Real.sin t * Real.cos t * remainder n β q t)) t := by
  have h := (hasDerivAt_interpolatedPressure hn β hq t).sub
    (((Real.hasDerivAt_sin t).pow 2).const_mul (β^2 * n / 4) |>.mul_const ((1-q)^2))
  convert h using 1
  first | rfl | ring

 

lemma pressure_sum_rule {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : 0 ≤ q) :
    pressure β n =
      (n : ℝ) * (∫ z : ℝ, Real.log (2 * Real.cosh (β * (Real.sqrt q * z))) ∂gaussianReal 0 1) +
      β^2 * n / 4 * (1-q)^2 - β^2 * n / 2 *
        ∫ t in (0 : ℝ)..(Real.pi/2), Real.sin t * Real.cos t * remainder n β q t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_correctedPressure hn β hq t)
    ((continuous_const.mul ((Real.continuous_sin.mul Real.continuous_cos).mul
      (continuous_remainder n β q))).intervalIntegrable 0 (Real.pi/2))
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Real.sin_pi_div_two, one_pow, mul_one, Real.sin_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, interpolatedPressure_pi_div_two, interpolatedPressure_zero n hβ q] at h
  linarith

lemma integrated_remainder_nonneg (n : ℕ) (β q : ℝ) :
    0 ≤ ∫ t in (0 : ℝ)..(Real.pi/2), Real.sin t * Real.cos t * remainder n β q t := by
  apply intervalIntegral.integral_nonneg (by positivity)
  intro t ht
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans (by linarith [Real.pi_pos]))
    · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  · exact remainder_nonneg n β q t

lemma pressure_le_trial {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : 0 ≤ q) :
    pressure β n ≤
      (n : ℝ) * (∫ z : ℝ, Real.log (2 * Real.cosh (β * (Real.sqrt q * z))) ∂gaussianReal 0 1) +
      β^2 * n / 4 * (1-q)^2 := by
  rw [pressure_sum_rule hn hβ hq]
  exact sub_le_self _ (mul_nonneg (by positivity) (integrated_remainder_nonneg n β q))

end ParisiInterpolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace ParisiInterpolation
open SKGaussian SKQAOA ParisiFinite

 

lemma freeEnergy_sum_rule {n : ℕ} (hn : 0 < n) {β : ℝ≥0} (hβ : 0 < β)
    (q : ℝ≥0) (hq : q ≤ 1) :
    freeEnergy β n = functional β (replicaSymmetricSchedule β q) -
      (β : ℝ) / 2 * ∫ t in (0 : ℝ)..(Real.pi/2),
        Real.sin t * Real.cos t * remainder n β q t := by
  have hβ' : (0 : ℝ) < β := hβ
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [freeEnergy, pressure_sum_rule hn hβ' q.coe_nonneg,
    replicaSymmetric_functional hβ q hq]
  simp only [terminal, integral_div]
  field_simp

lemma freeEnergy_le_functional {n : ℕ} (hn : 0 < n) {β : ℝ≥0} (hβ : 0 < β)
    (q : ℝ≥0) (hq : q ≤ 1) :
    freeEnergy β n ≤ functional β (replicaSymmetricSchedule β q) := by
  rw [freeEnergy_sum_rule hn hβ q hq]
  exact sub_le_self _ (mul_nonneg (by positivity) (integrated_remainder_nonneg n β q))

lemma limitingFreeEnergy_le_functional {β : ℝ≥0} (hβ : 0 < β)
    (q : ℝ≥0) (hq : q ≤ 1) :
    limitingFreeEnergy β ≤ functional β (replicaSymmetricSchedule β q) := by
  exact le_of_tendsto (tendsto_freeEnergy hβ) ((eventually_gt_atTop 0).mono fun n hn =>
    freeEnergy_le_functional hn hβ q hq)

end ParisiInterpolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

 

structure SmoothField where
  val : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  hasD1 : ∀ x, HasDerivAt val (d1 x) x
  hasD2 : ∀ x, HasDerivAt d1 (d2 x) x
  continuousD2 : Continuous d2
  bound1 : ℝ≥0
  bound2 : ℝ≥0
  normD1 : ∀ x, |d1 x| ≤ bound1
  normD2 : ∀ x, |d2 x| ≤ bound2

namespace SmoothField

lemma continuousVal (f : SmoothField) : Continuous f.val :=
  continuous_iff_continuousAt.mpr fun x => (f.hasD1 x).continuousAt

lemma continuousD1 (f : SmoothField) : Continuous f.d1 :=
  continuous_iff_continuousAt.mpr fun x => (f.hasD2 x).continuousAt

lemma lipschitz (f : SmoothField) : LipschitzWith f.bound1 f.val := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (f.hasD1 x).differentiableAt)
  intro x
  rw [(f.hasD1 x).deriv]
  exact_mod_cast f.normD1 x

lemma lipschitzD1 (f : SmoothField) : LipschitzWith f.bound2 f.d1 := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (f.hasD2 x).differentiableAt)
  intro x
  rw [(f.hasD2 x).deriv]
  exact_mod_cast f.normD2 x

end SmoothField

lemma exp_shift_near_le {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a x₀ s : ℝ) {x : ℝ} (hx : |x-x₀| ≤ 1) (z : ℝ) :
    Real.exp (a * f (x+s*z)) ≤
      Real.exp (|a| * (|f x₀| + L)) * Real.exp ((|a| * L * |s|) * |z|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hf.dist_le_mul (x+s*z) (x₀+s*z)
  simp only [Real.dist_eq, add_sub_add_right_eq_sub] at h
  have hh : |f (x+s*z)| ≤ |f x₀| + L + (L : ℝ)*|s| * |z| := by
    have ht := abs_add_le (f (x+s*z)-f (x₀+s*z)) (f (x₀+s*z))
    rw [sub_add_cancel] at ht
    have hb := shift_norm_le hf x₀ s z
    have hc := mul_le_mul_of_nonneg_left hx L.coe_nonneg
    nlinarith
  calc
    a*f (x+s*z) ≤ |a*f (x+s*z)| := le_abs_self _
    _ = |a| * |f (x+s*z)| := abs_mul _ _
    _ ≤ |a| * (|f x₀|+L+(L:ℝ)*|s| * |z|) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    _ = |a| * (|f x₀|+L)+(|a| * L*|s|)*|z| := by ring

 
def expMoment (a s : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.exp (a * f (x+s*z)) * g (x+s*z) ∂gaussianReal 0 1

lemma integrable_exp_weight {L : ℝ≥0} {f g : ℝ → ℝ}
    (hf : LipschitzWith L f) (hg : Continuous g) {M : ℝ} (hb : ∀ x, |g x| ≤ M)
    (a s x : ℝ) :
    Integrable (fun z => Real.exp (a*f (x+s*z))*g (x+s*z)) (gaussianReal 0 1) := by
  apply (integrable_exp_shift hf a x s).mul_bdd (by fun_prop)
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb (x+s*z)

lemma hasDerivAt_expMoment {L : ℝ≥0} {f f' g g' : ℝ → ℝ}
    (hf : LipschitzWith L f) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hb : ∀ x, |f' x| ≤ L)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    {M N : ℝ≥0} (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |g' x| ≤ N)
    (a s x₀ : ℝ) :
    HasDerivAt (expMoment a s f g)
      (∫ z, Real.exp (a*f (x₀+s*z)) *
        (a*f' (x₀+s*z)*g (x₀+s*z)+g' (x₀+s*z)) ∂gaussianReal 0 1) x₀ := by
  have hfc := hf.continuous
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball x₀ 1)
    (bound := fun z => (Real.exp (|a| * (|f x₀|+L)) *
      Real.exp ((|a| * L*|s|)*|z|)) * (|a| * L*M+N))
    (F' := fun x z => Real.exp (a*f (x+s*z)) * (a*f' (x+s*z)*g (x+s*z)+g' (x+s*z)))
    (Metric.ball_mem_nhds _ (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun x => by fun_prop
  · exact integrable_exp_weight hf hgc hM a s x₀
  · fun_prop
  · exact ae_of_all _ fun z x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (exp_shift_near_le hf a x₀ s (by simpa [Real.dist_eq] using hx.le) z)
      · apply (abs_add_le _ _).trans
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul
          (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg a)) (hM _)
          (abs_nonneg _) (by positivity)) (hN _)
      · exact abs_nonneg _
      · positivity
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z x _ => by
      have hfz := (hd (x+s*z)).comp x ((hasDerivAt_id x).add_const (s*z))
      have hgz := (hg (x+s*z)).comp x ((hasDerivAt_id x).add_const (s*z))
      convert (hfz.const_mul a).exp.mul hgz using 1 <;> first | rfl |
        (simp only [Function.comp_apply, id_eq, mul_one]; ring)

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

def expMass (a s : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.exp (a * f (x+s*z)) ∂gaussianReal 0 1

def tiltedMean (a s : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  expMoment a s f g x / expMass a s f x

lemma expMass_pos {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (a s x : ℝ) :
    0 < expMass a s f x := integral_exp_pos (integrable_exp_shift hf a x s)

@[simp] lemma tiltedMean_zero (s : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    tiltedMean 0 s f g x = ∫ z, g (x+s*z) ∂gaussianReal 0 1 := by
  simp [tiltedMean, expMass, expMoment]

lemma abs_tiltedMean_le {L : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (a s x : ℝ) :
    |tiltedMean a s f g x| ≤ M := by
  have hi := integrable_exp_weight hf hg hM a s x
  have hp := expMass_pos hf a s x
  unfold tiltedMean
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono hi.abs ((integrable_exp_shift hf a x s).const_mul M)
    (fun z => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le)
  simpa only [integral_const_mul, expMass] using h

lemma hasDerivAt_expMass (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (expMass a s f.val) (a*expMoment a s f.val f.d1 x) x := by
  have h := hasDerivAt_expMoment f.lipschitz f.hasD1 f.continuousD1 f.normD1
    (fun y => hasDerivAt_const y (1 : ℝ)) continuous_const
    (M := 1) (N := 0) (by intro; norm_num) (by intro; norm_num) a s x
  have he : expMoment a s f.val (fun _ => 1) = expMass a s f.val := by
    funext y
    simp [expMoment, expMass]
  rw [he] at h
  simpa only [one_mul, mul_one, add_zero, mul_left_comm _ a, integral_const_mul, expMoment] using h

lemma hasDerivAt_gaussianAverage {L : ℝ≥0} {f f' : ℝ → ℝ}
    (hf : LipschitzWith L f) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hb : ∀ x, |f' x| ≤ L) (s x : ℝ) :
    HasDerivAt (fun y => ∫ z, f (y+s*z) ∂gaussianReal 0 1)
      (∫ z, f' (x+s*z) ∂gaussianReal 0 1) x := by
  have hc := hf.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun _ => (L : ℝ)) (F' := fun y z => f' (y+s*z))
    univ_mem ?_ (integrable_shift hf x s) (by fun_prop) ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall fun _ => by fun_prop
  · exact ae_of_all _ fun z y _ => by simpa only [Real.norm_eq_abs] using hb (y+s*z)
  · exact ae_of_all _ fun z y _ => by
      convert (hd (y+s*z)).comp y ((hasDerivAt_id y).add_const (s*z)) using 1 <;>
        first | rfl | simp only [mul_one]

 

lemma hasDerivAt_step (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (step a s f.val) (tiltedMean a s f.val f.d1 x) x := by
  by_cases ha : a = 0
  · subst a
    have hs : step 0 s f.val = fun y => ∫ z, f.val (y+s*z) ∂gaussianReal 0 1 := by
      funext y
      simp [step]
    rw [hs, tiltedMean_zero]
    exact hasDerivAt_gaussianAverage f.lipschitz f.hasD1 f.continuousD1 f.normD1 s x
  · have h := ((hasDerivAt_expMass f a s x).log (expMass_pos f.lipschitz a s x).ne').div_const a
    have he : (a*expMoment a s f.val f.d1 x / expMass a s f.val x) / a =
        tiltedMean a s f.val f.d1 x := by unfold tiltedMean; field_simp
    rw [he] at h
    have hs : step a s f.val = fun y => Real.log (expMass a s f.val y) / a := by
      funext y
      simp [step, logMean, ha, expMass]
    rw [hs]
    exact h

lemma expMoment_add {L : ℝ≥0} {f g h : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |h x| ≤ N) (a s x : ℝ) :
    expMoment a s f (fun y => g y+h y) x = expMoment a s f g x + expMoment a s f h x := by
  simp only [expMoment, mul_add]
  exact integral_add (integrable_exp_weight hf hg hM a s x) (integrable_exp_weight hf hh hN a s x)

lemma expMoment_const_mul (a s : ℝ) (f g : ℝ → ℝ) (x c : ℝ) :
    expMoment a s f (fun y => c*g y) x = c*expMoment a s f g x := by
  simp only [expMoment, mul_left_comm _ c, integral_const_mul]

lemma tiltedMean_add {L : ℝ≥0} {f g h : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) (hh : Continuous h) {M N : ℝ}
    (hM : ∀ x, |g x| ≤ M) (hN : ∀ x, |h x| ≤ N) (a s x : ℝ) :
    tiltedMean a s f (fun y => g y+h y) x = tiltedMean a s f g x + tiltedMean a s f h x := by
  simp only [tiltedMean, expMoment_add hf hg hh hM hN, add_div]

lemma tiltedMean_const_mul (a s : ℝ) (f g : ℝ → ℝ) (x c : ℝ) :
    tiltedMean a s f (fun y => c*g y) x = c*tiltedMean a s f g x := by
  simp only [tiltedMean, expMoment_const_mul, mul_div_assoc]

lemma sq_bound {L : ℝ≥0} {g : ℝ → ℝ} (hg : ∀ x, |g x| ≤ L) (x : ℝ) :
    |g x ^ 2| ≤ (L : ℝ)^2 := by
  rw [abs_sq]
  nlinarith [hg x, abs_nonneg (g x), sq_abs (g x)]

lemma hasDerivAt_tiltedMean_d1 (f : SmoothField) (a s x : ℝ) :
    HasDerivAt (tiltedMean a s f.val f.d1)
      (tiltedMean a s f.val f.d2 x + a *
        (tiltedMean a s f.val (fun y => f.d1 y ^ 2) x - (tiltedMean a s f.val f.d1 x)^2)) x := by
  have h := hasDerivAt_expMoment f.lipschitz f.hasD1 f.continuousD1 f.normD1
    f.hasD2 f.continuousD2 f.normD1 f.normD2 a s x
  have he (y : ℝ) : a*f.d1 y*f.d1 y+f.d2 y = f.d2 y+a*f.d1 y^2 := by ring
  simp_rw [he] at h
  change HasDerivAt (expMoment a s f.val f.d1)
    (expMoment a s f.val (fun y => f.d2 y+a*f.d1 y^2) x) x at h
  rw [expMoment_add (g := f.d2) (h := fun y => a*f.d1 y^2) f.lipschitz f.continuousD2
    (by have hc := f.continuousD1; fun_prop) f.normD2
    (fun y => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (sq_bound f.normD1 y) (abs_nonneg a)),
    expMoment_const_mul] at h
  have hd := h.div (hasDerivAt_expMass f a s x) (expMass_pos f.lipschitz a s x).ne'
  convert hd using 1 <;> first | rfl | (unfold tiltedMean; field_simp; ring)

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ParisiFinite

lemma continuous_expMoment {L : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ≥0} (hM : ∀ x, |g x| ≤ M) (a s : ℝ) :
    Continuous (expMoment a s f g) := by
  have hfc := hf.continuous
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply continuousAt_of_dominated
    (bound := fun z => (Real.exp (|a| * (|f x₀|+L)) *
      Real.exp ((|a| * L * |s|)*|z|)) * M)
  · exact Eventually.of_forall fun x => (integrable_exp_weight hf hg hM a s x).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (exp_shift_near_le hf a x₀ s (by simpa [Real.dist_eq] using hx.le) z)
        (hM _) (abs_nonneg _) (by positivity)
  · exact ((integrable_exp_abs _).const_mul _).mul_const _
  · exact ae_of_all _ fun z => by fun_prop

lemma continuous_tiltedMean {L : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : Continuous g) {M : ℝ≥0} (hM : ∀ x, |g x| ≤ M) (a s : ℝ) :
    Continuous (tiltedMean a s f g) := by
  have he : expMass a s f = expMoment a s f (fun _ => 1) := by
    funext x
    simp [expMass, expMoment]
  have hc : Continuous (expMass a s f) := by
    rw [he]
    exact continuous_expMoment hf continuous_const (M := 1) (by intro; norm_num) a s
  exact (continuous_expMoment hf hg hM a s).div hc (fun x => (expMass_pos hf a s x).ne')

namespace SmoothField

 

def transform (f : SmoothField) (a s : ℝ) : SmoothField where
  val := step a s f.val
  d1 := tiltedMean a s f.val f.d1
  d2 := fun x => tiltedMean a s f.val f.d2 x + a *
    (tiltedMean a s f.val (fun y => f.d1 y^2) x - (tiltedMean a s f.val f.d1 x)^2)
  hasD1 := hasDerivAt_step f a s
  hasD2 := hasDerivAt_tiltedMean_d1 f a s
  continuousD2 := by
    have hc₁ := continuous_tiltedMean f.lipschitz f.continuousD1 f.normD1 a s
    have hc₂ := continuous_tiltedMean f.lipschitz f.continuousD2 f.normD2 a s
    have hcs := continuous_tiltedMean f.lipschitz (g := fun y => f.d1 y^2)
      (by have hc := f.continuousD1; fun_prop) (M := f.bound1^2) (sq_bound f.normD1) a s
    fun_prop
  bound1 := f.bound1
  bound2 := f.bound2 + 2 * Real.nnabs a * f.bound1^2
  normD1 := abs_tiltedMean_le f.lipschitz f.continuousD1 f.normD1 a s
  normD2 := by
    intro x
    have h1 := abs_tiltedMean_le f.lipschitz f.continuousD1 f.normD1 a s x
    have h2 := abs_tiltedMean_le f.lipschitz f.continuousD2 f.normD2 a s x
    have hs := abs_tiltedMean_le f.lipschitz (g := fun y => f.d1 y^2)
      (by have hc := f.continuousD1; fun_prop) (sq_bound f.normD1) a s x
    have hx : |(tiltedMean a s f.val f.d1 x)^2| ≤ (f.bound1:ℝ)^2 :=
      sq_bound (fun y => abs_tiltedMean_le f.lipschitz f.continuousD1 f.normD1 a s y) x
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hb : |tiltedMean a s f.val (fun y => f.d1 y^2) x - (tiltedMean a s f.val f.d1 x)^2| ≤
        |tiltedMean a s f.val (fun y => f.d1 y^2) x| + |(tiltedMean a s f.val f.d1 x)^2| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (tiltedMean a s f.val (fun y => f.d1 y^2) x) 0
        ((tiltedMean a s f.val f.d1 x)^2)
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_nnabs, NNReal.coe_pow]
    nlinarith [abs_nonneg a]

end SmoothField

lemma hasDerivAt_tanh_scaled (β x : ℝ) :
    HasDerivAt (fun y => Real.tanh (β*y)) (β/(Real.cosh (β*x))^2) x := by
  have hs := (Real.hasDerivAt_sinh (β*x)).comp x ((hasDerivAt_id x).const_mul β)
  have hc := (Real.hasDerivAt_cosh (β*x)).comp x ((hasDerivAt_id x).const_mul β)
  have h := hs.div hc (Real.cosh_pos (β*x)).ne'
  simp only [Function.comp_apply, mul_one] at h
  have he : (Real.cosh (β*x)*β*Real.cosh (β*x)-Real.sinh (β*x)*(Real.sinh (β*x)*β)) /
      Real.cosh (β*x)^2 = β/Real.cosh (β*x)^2 := by
    congr 1
    calc
      _ = β*(Real.cosh (β*x)^2-Real.sinh (β*x)^2) := by ring
      _ = β := by rw [Real.cosh_sq_sub_sinh_sq, mul_one]
  rw [he] at h
  have ht : (fun y => Real.tanh (β*y)) =
      (fun y => Real.sinh (β*y)) / (fun y => Real.cosh (β*y)) := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh _
  rw [ht]
  exact h

 
def terminalField (β : ℝ≥0) (hβ : 0 < β) : SmoothField where
  val := terminal β
  d1 := fun x => Real.tanh (β*x)
  d2 := fun x => (β : ℝ)/(Real.cosh (β*x))^2
  hasD1 := hasDerivAt_terminal hβ
  hasD2 := hasDerivAt_tanh_scaled β
  continuousD2 := continuous_const.div (by fun_prop)
    (fun x => pow_ne_zero 2 (Real.cosh_pos ((β:ℝ)*x)).ne')
  bound1 := 1
  bound2 := β
  normD1 := fun x => (Real.abs_tanh_lt_one _).le
  normD2 := by
    intro x
    rw [abs_of_nonneg (by positivity)]
    apply div_le_self β.coe_nonneg
    have hc := Real.one_le_cosh ((β:ℝ)*x)
    nlinarith

 

def smoothRecursion (β : ℝ≥0) (hβ : 0 < β) : Schedule → SmoothField
  | [] => terminalField β hβ
  | (a,d)::ls => (smoothRecursion β hβ ls).transform a (Real.sqrt d)

lemma smoothRecursion_val (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule) :
    (smoothRecursion β hβ ls).val = recursion β ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change step l.1 (Real.sqrt l.2) (smoothRecursion β hβ ls).val = _
      rw [ih]
      rfl

lemma smoothRecursion_bound1 (β : ℝ≥0) (hβ : 0 < β) (ls : Schedule) :
    (smoothRecursion β hβ ls).bound1 = 1 := by
  induction ls with
  | nil => rfl
  | cons l ls ih => exact ih

end ParisiFinite

end

end OAI
