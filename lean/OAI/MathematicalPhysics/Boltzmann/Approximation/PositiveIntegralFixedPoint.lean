import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Positive integral contraction along measurable characteristics

This lemma constructs a fixed point of a bounded positive source map.
The collision source and its quantitative estimates are supplied separately.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

abbrev Domain (P : Type*) := ℝ × P

def time (T t : ℝ) : ℝ := max 0 (min T t)

theorem time_bounds {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ time T t ∧ time T t ≤ T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

def value (T L : ℝ) (flow : ℝ → P → P) (f₀ : P → ℝ)
    (g : Domain P → ℝ) (z : Domain P) : ℝ :=
  Real.exp (-L * time T z.1) * f₀ (flow (-time T z.1) z.2) +
    ∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)

theorem measurable_value {T L : ℝ} (hT : 0 ≤ T) {flow : ℝ → P → P}
    (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀ : Measurable f₀) {g : Domain P → ℝ} (hg : Measurable g) :
    Measurable (value T L flow f₀ g) := by
  have ht : Measurable (fun z : Domain P => time T z.1) := by unfold time; fun_prop
  have hm : Measurable (fun z : Domain P =>
      ∫ r : ℝ, if 0 < r ∧ r ≤ time T z.1 then
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) else 0) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    have hfl : Measurable (fun q : Domain P × ℝ => flow (q.2 - time T q.1.1) q.1.2) :=
      hflow.comp ((measurable_snd.sub (ht.comp measurable_fst)).prodMk measurable_fst.snd)
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (ht.comp measurable_fst))
    · have he : Measurable (fun q : Domain P × ℝ => Real.exp (-L * (time T q.1.1 - q.2))) := by
        unfold time
        fun_prop
      exact he.mul (hg.comp (measurable_snd.prodMk hfl))
    · exact measurable_const
  have he (z : Domain P) : (∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) =
      ∫ r : ℝ, if 0 < r ∧ r ≤ time T z.1 then
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) else 0 := by
    rw [intervalIntegral.integral_of_le (time_bounds hT z.1).1, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by simp only [Set.indicator_apply, Set.mem_Ioc])
  unfold value
  simp_rw [he]
  have he : Measurable (fun z : Domain P => Real.exp (-L * time T z.1)) := by
    unfold time
    fun_prop
  exact (he.mul (hf₀.comp (hflow.comp ((ht.neg).prodMk measurable_snd)))).add hm

omit [MeasurableSpace P] in
theorem value_bounds {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hS : 0 ≤ S) (flow : ℝ → P → P) {f₀ : P → ℝ}
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) {g : Domain P → ℝ}
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ S)
    (z : Domain P) : 0 ≤ value T L flow f₀ g z ∧ value T L flow f₀ g z ≤ A + T * S := by
  have ht := time_bounds hT z.1
  have he (r : ℝ) (hr : r ∈ Icc 0 (time T z.1)) :
      0 ≤ Real.exp (-L * (time T z.1 - r)) ∧ Real.exp (-L * (time T z.1 - r)) ≤ 1 := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [hr.2])⟩
  have hi : (∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) ≤ S * time T z.1 := by
    apply (le_abs_self _).trans
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0)
      (b := time T z.1) (C := S) (f := fun r =>
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2))
      (fun r hr => by
        rw [uIoc_of_le ht.1] at hr
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg _).1)]
        exact (mul_le_mul_of_nonneg_right (he r ⟨hr.1.le, hr.2⟩).2 (hg _).1).trans
          (by simpa using (hg _).2))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using h
  constructor
  · exact add_nonneg (mul_nonneg (Real.exp_pos _).le (hf₀ _).1)
      (intervalIntegral.integral_nonneg ht.1 (fun r _ => mul_nonneg (Real.exp_pos _).le (hg _).1))
  · have hinit : Real.exp (-L * time T z.1) * f₀ (flow (-time T z.1) z.2) ≤ A :=
      (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith)) (hf₀ _).1).trans
        (by simpa using (hf₀ _).2)
    exact (add_le_add hinit hi).trans (by nlinarith)

theorem damped_integrable {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {g : Domain P → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S)
    (z : Domain P) : IntervalIntegrable (fun r =>
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) volume 0 (time T z.1) := by
  apply (intervalIntegrable_const (c := S)).mono_fun'
  · have hm : Measurable (fun r : ℝ => flow (r - time T z.1) z.2) :=
      hflow.comp ((measurable_id.sub measurable_const).prodMk measurable_const)
    have he : Measurable (fun r : ℝ => Real.exp (-L * (time T z.1 - r))) := by fun_prop
    exact (he.mul (hgm.comp (measurable_id.prodMk hm))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [uIoc_of_le (time_bounds hT z.1).1] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hg _)

theorem value_difference {T L S D : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z - h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z - value T L flow f₀ h z| ≤ T * D := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL hflow hgm hg z
  have hhi := damped_integrable hT hL hflow hhm hh z
  unfold value
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hgi hhi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := time T z.1)
    (C := D) (f := fun r =>
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) -
      Real.exp (-L * (time T z.1 - r)) * h (r, flow (r - time T z.1) z.2))
    (fun r hr => by
      rw [uIoc_of_le ht.1] at hr
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
      exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hgh _))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb
  exact hb.trans (by nlinarith)

/-- Positive Picard iteration converges in the complete sup-norm space. -/
theorem exists_fixed_point {T L A R S K : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hball : A + T * S ≤ R) (hsmall : T * K < 1)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, 0 ≤ source f z ∧ source f z ≤ S)
    (hsl : ∀ f g z, |source f z - source g z| ≤ K * dist f g) :
    ∃ f : BoundedMeasurable.PositiveBall (Domain P) R,
      ∀ z, f.val z = value T L flow f₀ (source f) z := by
  let step : BoundedMeasurable.PositiveBall (Domain P) R →
      BoundedMeasurable.PositiveBall (Domain P) R := fun f =>
    ⟨BoundedMeasurable.ofBounded (Domain P) (value T L flow f₀ (source f))
      (measurable_value hT hflow hf₀m (hsm f)) (A + T * S)
      (fun z => by
        rw [abs_of_nonneg (value_bounds hT hL hA hS flow hf₀ (hsb f) z).1]
        exact (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2),
      fun z => ⟨(value_bounds hT hL hA hS flow hf₀ (hsb f) z).1,
        (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2.trans hball⟩⟩
  have hc : ContractingWith ⟨T * K, mul_nonneg hT hK⟩ step := by
    constructor
    · exact hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro f g
      change dist (step f).val (step g).val ≤ (T * K) * dist f g
      apply BoundedMeasurable.dist_le (Domain P) (by positivity)
      intro z
      have h := value_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
        (hsm f) (hsm g)
        (fun z => by rw [abs_of_nonneg (hsb f z).1]; exact (hsb f z).2)
        (fun z => by rw [abs_of_nonneg (hsb g z).1]; exact (hsb g z).2)
        (hsl f g) z
      simpa only [step, BoundedMeasurable.ofBounded_apply, mul_assoc] using h
  let zero : BoundedMeasurable.PositiveBall (Domain P) R :=
    ⟨BoundedMeasurable.ofBounded (Domain P) (fun _ => 0) measurable_const 0
      (fun _ => by simp), fun _ => ⟨le_rfl, hR⟩⟩
  let : Nonempty (BoundedMeasurable.PositiveBall (Domain P) R) := ⟨zero⟩
  refine ⟨hc.fixedPoint, ?_⟩
  intro z
  have he := congrArg (fun f : BoundedMeasurable.PositiveBall (Domain P) R => f.val z)
    hc.fixedPoint_isFixedPt
  exact he.symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Order and dominated convergence for positive characteristic integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_mono {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, f₀ p ≤ k₀ p)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, g z ≤ h z)
    (z : Domain P) : value T L flow f₀ g z ≤ value T L flow k₀ h z := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hfk _) (Real.exp_pos _).le
  · apply intervalIntegral.integral_mono_on (time_bounds hT z.1).1
      (damped_integrable hT hL hflow hgm hg z) (damped_integrable hT hL hflow hhm hh z)
    intro r _
    exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le

theorem value_tendsto {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g : ℕ → Domain P → ℝ} {h : Domain P → ℝ}
    (hgm : ∀ n, Measurable (g n)) (hg : ∀ n z, |g n z| ≤ S)
    (hlim : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (h z)))
    (z : Domain P) : Tendsto (fun n => value T L flow f₀ (g n) z) atTop
      (𝓝 (value T L flow f₀ h z)) := by
  apply tendsto_const_nhds.add
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => S)
  · exact .of_forall (fun n => (damped_integrable hT hL hflow (hgm n) (hg n) z).def'.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    apply ae_of_all
    intro r hr
    rw [uIoc_of_le (time_bounds hT z.1).1] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hg n _)
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun r _ => tendsto_const_nhds.mul (hlim _))

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Removing the auxiliary exponential weight from a mild solution -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.PositiveIntegral
variable {P : Type*}

theorem value_rescale {T : ℝ} (hT : 0 ≤ T) (a L : ℝ) (flow : ℝ → P → P)
    (f₀ : P → ℝ) (g : Domain P → ℝ) (z : Domain P) :
    Real.exp (a*time T z.1) * value T (a+L) flow f₀
      (fun w => Real.exp (-a*time T w.1)*g w) z = value T L flow f₀ g z := by
  have ht := time_bounds hT z.1
  have hi : Real.exp (a*time T z.1)*Real.exp (-(a+L)*time T z.1) =
      Real.exp (-L*time T z.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he (r : ℝ) : Real.exp (a*time T z.1)*Real.exp (-(a+L)*(time T z.1-r))*Real.exp (-a*r) =
      Real.exp (-L*(time T z.1-r)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold value
  rw [mul_add,← mul_assoc,hi,← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  have hrT : r ≤ T := hr.2.trans ht.2
  have hrt : time T r = r := by
    unfold time
    rw [min_eq_right hrT,max_eq_right hr.1]
  dsimp only
  rw [hrt]
  calc
    _ = (Real.exp (a*time T z.1)*Real.exp (-(a+L)*(time T z.1-r))*Real.exp (-a*r))*
      g (r,flow (r-time T z.1) z.2) := by ring
    _ = _ := by rw [he]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Uniqueness on a common bounded interval for the positive integral map -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem fixed_point_unique {T L R S K : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hsmall : T * K < 1)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, |source f z| ≤ S)
    (hsl : ∀ f g z, |source f z - source g z| ≤ K * dist f g)
    {f g : BoundedMeasurable.PositiveBall (Domain P) R}
    (hf : ∀ z, f.val z = value T L flow f₀ (source f) z)
    (hg : ∀ z, g.val z = value T L flow f₀ (source g) z) : f = g := by
  have hd : dist f g ≤ (T * K) * dist f g := by
    change dist f.val g.val ≤ _
    apply BoundedMeasurable.dist_le (Domain P) (by positivity)
    intro z
    rw [hf, hg]
    have h := value_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
      (hsm f) (hsm g) (hsb f) (hsb g) (hsl f g) z
    simpa only [mul_assoc] using h
  have hz : dist f g = 0 := by nlinarith [dist_nonneg (x := f) (y := g)]
  exact dist_eq_zero.mp hz

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Dependence of the characteristic map on its initial value -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_difference_initial {T L S D I : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hD : 0 ≤ D) (_hI : 0 ≤ I)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, |f₀ p-k₀ p| ≤ I)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z-h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z-value T L flow k₀ h z| ≤ I+T*D := by
  have hsource := value_difference hT hL hD hflow f₀ hgm hhm hg hh hgh z
  have hinitial : |value T L flow f₀ h z-value T L flow k₀ h z| ≤ I := by
    have heq : value T L flow f₀ h z-value T L flow k₀ h z =
        Real.exp (-L*time T z.1) * (f₀ (flow (-time T z.1) z.2)-k₀ (flow (-time T z.1) z.2)) := by
      unfold value
      ring
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L*time T z.1) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (time_bounds hT z.1).1)
    exact (mul_le_mul he (hfk _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul I)
  exact (abs_sub_le _ _ _).trans ((add_le_add hsource hinitial).trans_eq (add_comm _ _))

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Finite sums of positive characteristic integrals -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P]

theorem value_finsetSum {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (s : Finset I) (f₀ : I → P → ℝ) (g : I → Domain P → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hg : ∀ i ∈ s, ∀ z, |g i z| ≤ S)
    (z : Domain P) :
    ∑ i ∈ s, value T L flow (f₀ i) (g i) z =
      value T L flow (fun p => ∑ i ∈ s, f₀ i p) (fun q => ∑ i ∈ s, g i q) z := by
  unfold value
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum
    (fun i hi => damped_integrable hT hL hflow (hgm i hi) (hg i hi) z)]
  apply intervalIntegral.integral_congr
  intro r _
  exact (Finset.mul_sum s _ _).symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Countable positive sums in the characteristic equation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P] [Countable I]

theorem hasSum_value {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : I → P → ℝ) (hf₀ : ∀ p, Summable (fun i => f₀ i p))
    (g : I → Domain P → ℝ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i z, 0 ≤ g i z ∧ g i z ≤ S)
    (hgs : ∀ z, Summable (fun i => g i z)) (hgb : ∀ z, (∑' i, g i z) ≤ S)
    (z : Domain P) : HasSum (fun i => value T L flow (f₀ i) (g i) z)
      (value T L flow (fun p => ∑' i, f₀ i p) (fun q => ∑' i, g i q) z) := by
  have hsm : Measurable (fun q => ∑' i, g i q) := Measurable.tsum hgm
  have hsa (q) : |∑' i, g i q| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hg i q).1))]
    exact hgb q
  have hgi (i) := damped_integrable hT hL hflow (hgm i)
    (fun q => by rw [abs_of_nonneg (hg i q).1]; exact (hg i q).2) z
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := time T z.1) (μ := volume)
    (F := fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (f := fun r => Real.exp (-L * (time T z.1 - r)) *
      ∑' i, g i (r, flow (r - time T z.1) z.2))
    (fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (fun i => (hgi i).def'.aestronglyMeasurable)
    (fun i => ae_of_all _ (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg i _).1)]))
    (ae_of_all _ (fun r _ => (hgs _).mul_left _))
    (by
      simpa only [tsum_mul_left] using damped_integrable hT hL hflow hsm hsa z)
    (ae_of_all _ (fun r _ => (hgs _).hasSum.mul_left _))
  exact ((hf₀ _).hasSum.mul_left (Real.exp (-L * time T z.1))).add hi

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Positive mass of an integral is bounded by the integral of positive mass -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem positive_marginal_bound {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hfm : Measurable f) (hfi : Integrable f (μ.prod ν)) :
    (∫⁻ x, ENNReal.ofReal (∫ y, f (x,y) ∂ν) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (f z) ∂μ.prod ν := by
  rw [lintegral_prod _ hfm.ennreal_ofReal.aemeasurable]
  exact lintegral_mono_ae (hfi.prod_right_ae.mono (fun x hx => Published.ofReal_integral_le_lintegral hx))

end BoltzmannNonuniqueness

end

end

end OAI
