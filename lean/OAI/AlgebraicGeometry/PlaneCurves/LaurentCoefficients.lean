import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring
import OAI.AlgebraicGeometry.PlaneCurves.Automorphic
import OAI.AlgebraicGeometry.PlaneCurves.Intervals

namespace OAI

/-!
# Analytic Laurent coefficients, integral transforms, and recurrences
-/

section

/-!
# Genuine analytic Laurent coefficients
-/

namespace Nagata.W09

open Complex Real Metric
open scoped Topology

/-- The actual kth Laurent coefficient obtained on the circle of radius r. -/
noncomputable def analyticLaurentCoeff (r : ℝ) (f : ℂ → ℂ) (k : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ z in C(0, r), z ^ (-k - 1) * f z

theorem differentiableAt_laurentIntegrand {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w => w ^ (-k - 1) * f w) z :=
  (differentiableAt_zpow.mpr (Or.inl hz)).mul (hf z hz)

theorem circleIntegrable_laurentIntegrand {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    CircleIntegrable (fun z => z ^ (-k - 1) * f z) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact (differentiableAt_laurentIntegrand hf k hz0).continuousAt.continuousWithinAt

theorem analyticLaurentCoeff_add {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hg : ∀ z, z ≠ 0 → DifferentiableAt ℂ g z) (k : ℤ) :
    analyticLaurentCoeff r (f + g) k = analyticLaurentCoeff r f k + analyticLaurentCoeff r g k := by
  unfold analyticLaurentCoeff
  simp only [Pi.add_apply, mul_add]
  rw [circleIntegral.integral_add (circleIntegrable_laurentIntegrand hr hf k)
    (circleIntegrable_laurentIntegrand hr hg k), mul_add]

theorem analyticLaurentCoeff_smul (r : ℝ) (a : ℂ) (f : ℂ → ℂ) (k : ℤ) :
    analyticLaurentCoeff r (a • f) k = a * analyticLaurentCoeff r f k := by
  unfold analyticLaurentCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : (fun z : ℂ => z ^ (-k - 1) * (a * f z)) =
      (fun z => a * (z ^ (-k - 1) * f z)) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

/-- Actual Laurent-coefficient extraction at radius one is a linear map on the
existing analytic automorphic-section space. -/
noncomputable def laurentCoefficientMap (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Nagata.W08.automorphicSections τ n γ →ₗ[ℂ] (ℤ → ℂ) where
  toFun f k := analyticLaurentCoeff 1 f.val k
  map_add' f g := by
    funext k
    exact analyticLaurentCoeff_add zero_lt_one f.property.2.1 g.property.2.1 k
  map_smul' a f := by
    funext k
    exact analyticLaurentCoeff_smul 1 a f.val k

@[simp] theorem laurentCoefficientMap_apply (τ : ℂ) (n : ℤ) (γ : ℂ)
    (f : Nagata.W08.automorphicSections τ n γ) (k : ℤ) :
    laurentCoefficientMap τ n γ f k = analyticLaurentCoeff 1 f.val k := rfl

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Metric MeasureTheory Filter
open scoped Topology

/-- Countable circle-integral exchange under an actual summable bound on the
circle. This is dominated convergence applied to the literal parametrization. -/
theorem hasSum_circleIntegral_of_summable_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => ∮ z in C(0, r), F i z) (∮ z in C(0, r), f z) := by
  unfold circleIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => r * B i)
  · intro i
    exact ((hcont i).circleIntegrable hr.le).out.aestronglyMeasurable_restrict_uIoc
  · intro i
    exact ae_of_all _ fun θ _ => by
      simp only [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I,
        mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hbound i _ (circleMap_mem_sphere 0 hr.le θ)) hr.le
  · exact ae_of_all _ fun _ _ => hB.mul_left r
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun θ _ =>
      (hsum _ (circleMap_mem_sphere 0 hr.le θ)).const_smul _

/-- Actual Laurent coefficients commute with a pointwise series whose weighted
terms have a summable uniform bound on the integration circle. -/
theorem hasSum_analyticLaurentCoeff_of_summable_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖z ^ (-k - 1) * F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => analyticLaurentCoeff r (F i) k) (analyticLaurentCoeff r f k) := by
  have hpow : ContinuousOn (fun z : ℂ => z ^ (-k - 1)) (sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    exact (differentiableAt_zpow.mpr (Or.inl hz0)).continuousAt.continuousWithinAt
  exact (hasSum_circleIntegral_of_summable_bound hr
    (fun i z => z ^ (-k - 1) * F i z) (fun z => z ^ (-k - 1) * f z) B hB
    (fun i => hpow.mul (hcont i)) hbound
    (fun z hz => (hsum z hz).mul_left _)).mul_left _

/-- The convenient unweighted version: a summable uniform bound for the original
series suffices for every fixed Laurent coefficient. -/
theorem hasSum_analyticLaurentCoeff_of_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => analyticLaurentCoeff r (F i) k) (analyticLaurentCoeff r f k) := by
  apply hasSum_analyticLaurentCoeff_of_summable_bound hr F f k
    (fun i => r ^ (-k - 1) * B i) (hB.mul_left _) hcont
  · intro i z hz
    have hnorm : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_zpow, hnorm]
    exact mul_le_mul_of_nonneg_left (hbound i z hz) (zpow_pos hr _).le
  · exact hsum

/-- Every point on a positive-radius circle has an angle in one fixed compact
period; this permits the fixed-disk theta majorant to control the whole circle. -/
theorem exists_circle_angle_of_mem_sphere {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ sphere 0 r) :
    ∃ θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), circleMap 0 r θ = z := by
  have hmem : z ∈ circleMap 0 r '' Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [image_circleMap_Ioc, abs_of_pos hr]
    exact hz
  exact hmem

/-- The circle-bound criterion in the exact fixed-angle form used by the
normalized theta series on the moving physical circle r=z0. -/
theorem hasSum_analyticLaurentCoeff_of_parametric_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i θ, θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) →
      ‖F i (circleMap 0 r θ)‖ ≤ B i)
    (hsum : ∀ θ, θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) →
      HasSum (fun i => F i (circleMap 0 r θ)) (f (circleMap 0 r θ))) :
    HasSum (fun i => analyticLaurentCoeff r (F i) k) (analyticLaurentCoeff r f k) := by
  apply hasSum_analyticLaurentCoeff_of_bound hr F f k B hB hcont
  · intro i z hz
    obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere hr hz
    exact hbound i θ hθ
  · intro z hz
    obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere hr hz
    exact hsum θ hθ

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Real Metric

/-- Agreement on the actual integration circle gives agreement of coefficients. -/
theorem analyticLaurentCoeff_congr {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℂ}
    (h : Set.EqOn f g (Metric.sphere 0 r)) (k : ℤ) :
    analyticLaurentCoeff r f k = analyticLaurentCoeff r g k := by
  unfold analyticLaurentCoeff
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [h hz]

/-- Change of parametrization for dilation by a real scalar. -/
theorem circleIntegral_scale_real (a r : ℝ) (f : ℂ → ℂ) :
    (∮ z in C(0, a * r), f z) =
      (a : ℂ) * ∮ z in C(0, r), f ((a : ℂ) * z) := by
  unfold circleIntegral
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        (a : ℂ) * (deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [deriv_circleMap, circleMap, zero_add,
        Complex.ofReal_mul, smul_eq_mul, mul_assoc]
    _ = _ := by
      simpa only [smul_eq_mul] using intervalIntegral.integral_const_mul (a : ℂ)
        (fun θ => deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ))

/-- Multiplication by z^(-n) shifts the actual Laurent coefficient index by n. -/
theorem analyticLaurentCoeff_zpow_mul {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (n k : ℤ) :
    analyticLaurentCoeff r (fun z => z ^ (-n) * f z) k =
      analyticLaurentCoeff r f (k + n) := by
  unfold analyticLaurentCoeff
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  dsimp only
  rw [← mul_assoc, ← zpow_add₀ hz0]
  congr 2
  omega

/-- Dilation transforms the genuine circle coefficient by the corresponding
integer power. This identity itself does not require holomorphy. -/
theorem analyticLaurentCoeff_comp_pos_mul {a : ℝ} (ha : 0 < a)
    (r : ℝ) (f : ℂ → ℂ) (k : ℤ) :
    analyticLaurentCoeff r (fun z => f ((a : ℂ) * z)) k =
      (a : ℂ) ^ k * analyticLaurentCoeff (a * r) f k := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold analyticLaurentCoeff
  rw [circleIntegral_scale_real]
  have hfun : (fun z : ℂ => ((a : ℂ) * z) ^ (-k - 1) * f ((a : ℂ) * z)) =
      fun z => (a : ℂ) ^ (-k - 1) * (z ^ (-k - 1) * f ((a : ℂ) * z)) := by
    funext z
    rw [mul_zpow]
    ring
  rw [hfun, circleIntegral.integral_const_mul]
  have hpow : (a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1) = 1 := by
    have hp : (a : ℂ) ^ k * (a : ℂ) = (a : ℂ) ^ (k + 1) := by
      rw [zpow_add₀ ha0, zpow_one]
    rw [hp, ← zpow_add₀ ha0]
    simp only [show k + 1 + (-k - 1) = 0 by omega, zpow_zero]
  calc
    _ = ((a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1)) *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∮ z in C(0, r), z ^ (-k - 1) * f ((a : ℂ) * z)) := by rw [hpow, one_mul]
    _ = _ := by ring

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Metric Set

/-- Cauchy-Goursat on a genuine closed annulus, specialized to functions
holomorphic on the whole punctured plane. -/
theorem circleIntegral_radius_eq_of_holomorphic_punctured
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) :
    (∮ z in C(0, R), f z) = ∮ z in C(0, r), f z := by
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle
    Set.countable_empty
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.2 (by simpa using hr)
    exact (hf z hz0).continuousAt.continuousWithinAt
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.1.2 (by simpa using hr.le)
    exact hf z hz0

/-- Laurent coefficients of a genuinely holomorphic punctured-plane function
are independent of the positive circle radius. -/
theorem analyticLaurentCoeff_radius_independent
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    analyticLaurentCoeff r f k = analyticLaurentCoeff s f k := by
  unfold analyticLaurentCoeff
  congr 1
  rcases le_total r s with hrs | hsr
  · exact (circleIntegral_radius_eq_of_holomorphic_punctured hr hrs
      (fun z hz => differentiableAt_laurentIntegrand hf k hz)).symm
  · exact circleIntegral_radius_eq_of_holomorphic_punctured hs hsr
      (fun z hz => differentiableAt_laurentIntegrand hf k hz)

end Nagata.W09

end

section

/-!
# Concrete coefficient sequences on one Laurent residue class
-/
namespace Nagata.W09

open Nagata.W08

variable {F : Type*} [CommGroupWithZero F]

/-- Extend the explicit orbit formula by zero outside the residue class of K. -/
noncomputable def supportedOrbitCoefficient (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ) : F :=
  if n ∣ k - K then orbitValue τ γ n K c₀ ((k - K) / n) else 0

@[simp] theorem supportedOrbitCoefficient_initial (τ γ : F) (n K : ℤ) (c₀ : F) :
    supportedOrbitCoefficient τ γ n K c₀ K = c₀ := by
  simp [supportedOrbitCoefficient]

theorem supportedOrbitCoefficient_support (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : supportedOrbitCoefficient τ γ n K c₀ k ≠ 0) : n ∣ k - K := by
  by_contra hdiv
  simp [supportedOrbitCoefficient, hdiv] at h

theorem supportedOrbitCoefficient_residue (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : supportedOrbitCoefficient τ γ n K c₀ k ≠ 0) : k % n = K % n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (supportedOrbitCoefficient_support τ γ n K c₀ k h))

theorem supportedOrbitCoefficient_on_orbit (τ γ : F) {n : ℤ} (hn : n ≠ 0)
    (K : ℤ) (c₀ : F) (p : ℤ) :
    supportedOrbitCoefficient τ γ n K c₀ (K + n * p) = orbitValue τ γ n K c₀ p := by
  have hdiff : K + n * p - K = n * p := by omega
  simp [supportedOrbitCoefficient, hdiff, Int.mul_ediv_cancel_left p hn]

/-- The supported sequence satisfies the original one-step Laurent recurrence
at every integer, including positions outside its support. -/
theorem supportedOrbitCoefficient_recurrence (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    {n : ℤ} (hn : n ≠ 0) (K : ℤ) (c₀ : F) (k : ℤ) :
    supportedOrbitCoefficient τ γ n K c₀ (k + n) =
      γ⁻¹ * τ ^ k * supportedOrbitCoefficient τ γ n K c₀ k := by
  by_cases hk : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hk
    have hkp : k = K + n * p := by omega
    have hnext : k + n = K + n * (p + 1) := by
      rw [Int.mul_add, Int.mul_one]
      omega
    rw [hnext, hkp, supportedOrbitCoefficient_on_orbit τ γ hn,
      supportedOrbitCoefficient_on_orbit τ γ hn, orbitValue_add_one τ γ hτ hγ]
  · have hnext : ¬ n ∣ k + n - K := by
      intro h
      apply hk
      have hd := Int.dvd_sub h (Int.dvd_refl n)
      convert hd using 1
      omega
    simp [supportedOrbitCoefficient, hk, hnext]

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Metric

/-- The multiplier equation gives the exact coefficient balance by genuine
circle integration. Positive real tau is the manuscript's actual parameter. -/
theorem analyticLaurentCoeff_balance_pos_real {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (f : Nagata.W08.automorphicSections (τ : ℂ) n γ) (k : ℤ) :
    (τ : ℂ) ^ k * analyticLaurentCoeff 1 f.val k =
      γ * analyticLaurentCoeff 1 f.val (k + n) := by
  have hcomp : analyticLaurentCoeff 1 (fun z => f.val ((τ : ℂ) * z)) k =
      γ * analyticLaurentCoeff 1 f.val (k + n) := by
    calc
      _ = analyticLaurentCoeff 1 (γ • (fun z => z ^ (-n) * f.val z)) k := by
        apply analyticLaurentCoeff_congr (by norm_num)
        intro z hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          simp at hz
        simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using f.property.2.2 z hz0
      _ = γ * analyticLaurentCoeff 1 (fun z => z ^ (-n) * f.val z) k :=
        analyticLaurentCoeff_smul 1 γ _ k
      _ = γ * analyticLaurentCoeff 1 f.val (k + n) := by
        rw [analyticLaurentCoeff_zpow_mul zero_lt_one]
  have hdilate := analyticLaurentCoeff_comp_pos_mul hτ 1 f.val k
  rw [mul_one, analyticLaurentCoeff_radius_independent hτ zero_lt_one f.property.2.1 k] at hdilate
  exact hdilate.symm.trans hcomp

/-- The genuine analytic extraction map satisfies the exact source recurrence;
no recurrence is assumed as a field of the analytic section space. -/
theorem laurentCoefficientMap_recurrence_pos_real {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (hγ : γ ≠ 0)
    (f : Nagata.W08.automorphicSections (τ : ℂ) n γ) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n γ f (k + n) =
      γ⁻¹ * (τ : ℂ) ^ k * laurentCoefficientMap (τ : ℂ) n γ f k := by
  exact Nagata.W08.recurrence_of_coefficient_balance (τ : ℂ) γ hγ n
    (fun j => analyticLaurentCoeff 1 f.val j)
    (analyticLaurentCoeff_balance_pos_real hτ n γ f) k

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Metric

/-- The actual circle integral extracts precisely one Laurent monomial. -/
theorem analyticLaurentCoeff_monomial {r : ℝ} (hr : 0 < r) (j k : ℤ) :
    analyticLaurentCoeff r (fun z => z ^ j) k = if j = k then 1 else 0 := by
  unfold analyticLaurentCoeff
  have hi : (∮ z in C(0, r), z ^ (-k - 1) * z ^ j) =
      ∮ z in C(0, r), z ^ (j - k - 1) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    dsimp only
    rw [← zpow_add₀ hz0]
    congr 1
    omega
  rw [hi]
  by_cases hjk : j = k
  · subst j
    simp only [sub_self, zero_sub, zpow_neg_one]
    have hcircle : (∮ z in C(0, r), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    have hconst : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [hcircle, inv_mul_cancel₀ hconst]
    simp
  · rw [ite_eq_right hjk]
    have hne : j - k - 1 ≠ -1 := by omega
    have hcircle : (∮ z in C(0, r), z ^ (j - k - 1)) = 0 := by
      simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hne (0 : ℂ) 0 r
    rw [hcircle, mul_zero]

/-- Scalar Laurent monomials have their literal scalar as the extracted
coefficient, and zero in every other integer degree. -/
theorem analyticLaurentCoeff_smul_monomial {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j k : ℤ) :
    analyticLaurentCoeff r (fun z => a * z ^ j) k = if j = k then a else 0 := by
  change analyticLaurentCoeff r (a • (fun z : ℂ => z ^ j)) k = _
  rw [analyticLaurentCoeff_smul, analyticLaurentCoeff_monomial hr]
  split <;> simp

end Nagata.W09

end

section

namespace Nagata.W09

/-- A genuine Laurent recurrence sequence is determined by its coefficients in
one complete residue interval. This proves uniqueness of coefficients, not
existence or injectivity of analytic Laurent expansion. -/
theorem laurent_recurrence_eq_of_thetaIndices
    {F : Type*} [CommGroupWithZero F] (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (U : ℝ) {n : ℤ} (hn : 0 < n) (c d : ℤ → F)
    (hc : ∀ k, c (k + n) = γ⁻¹ * τ ^ k * c k)
    (hd : ∀ k, d (k + n) = γ⁻¹ * τ ^ k * d k)
    (hinitial : ∀ K ∈ thetaIndices U n, c K = d K) : c = d := by
  funext k
  obtain ⟨K, hK, hres⟩ := exists_thetaIndex_modEq U hn k
  have hdiv : n ∣ k - K := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hres.symm)
  let p := (k - K) / n
  have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
  have hkp : k = K + n * p := by omega
  rw [hkp, Nagata.W08.laurent_recurrence_all_int τ γ hτ hγ n c hc,
    Nagata.W08.laurent_recurrence_all_int τ γ hτ hγ n d hd, hinitial K hK]

end Nagata.W09

end

section

namespace Nagata.W09

open Complex Metric

private theorem continuousOn_scalar_monomial_circle {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j : ℤ) : ContinuousOn (fun z : ℂ => a * z ^ j) (sphere 0 r) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact ((differentiableAt_const a).mul
    (differentiableAt_zpow.mpr (Or.inl hz0))).continuousAt.continuousWithinAt

/-- Coefficient extraction from a genuinely normally convergent Laurent-monomial
series is the sum of the literal coefficients in the matching integer degree. -/
theorem hasSum_analyticLaurentCoeff_of_monomial_series
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (k : ℤ) :
    HasSum (fun i => if N i = k then a i else 0) (analyticLaurentCoeff r f k) := by
  simpa only [analyticLaurentCoeff_smul_monomial hr] using
    hasSum_analyticLaurentCoeff_of_bound hr (fun i z => a i * z ^ N i) f k B hB
      (fun i => continuousOn_scalar_monomial_circle hr (a i) (N i)) hbound hsum

/-- With distinct exponents, the analytic coefficient equals the corresponding
coefficient of the actual convergent monomial series. -/
theorem analyticLaurentCoeff_monomial_series_at
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (hN : Function.Injective N)
    (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (i₀ : ι) :
    analyticLaurentCoeff r f (N i₀) = a i₀ := by
  have h := hasSum_analyticLaurentCoeff_of_monomial_series hr a N f B hB hbound hsum (N i₀)
  have hs : HasSum (fun i => if N i = N i₀ then a i else 0) (a i₀) := by
    have hz : ∀ i, i ≠ i₀ → (if N i = N i₀ then a i else 0) = 0 := by
      intro i hi
      exact ite_eq_right (fun heq => hi (hN heq))
    simpa only [ite_true] using hasSum_single i₀ hz
  exact h.unique hs

/-- No analytic coefficient outside the actual exponent range can occur. -/
theorem analyticLaurentCoeff_monomial_series_eq_zero
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z))
    (k : ℤ) (hk : k ∉ Set.range N) : analyticLaurentCoeff r f k = 0 := by
  have h := hasSum_analyticLaurentCoeff_of_monomial_series hr a N f B hB hbound hsum k
  have hz : (fun i => if N i = k then a i else 0) = fun _ => (0 : ℂ) := by
    funext i
    exact ite_eq_right (fun heq => hk ⟨i, heq⟩)
  rw [hz] at h
  exact h.unique hasSum_zero

end Nagata.W09

end

end OAI
