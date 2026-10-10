import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
import OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

def radialTestCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩

@[simp] theorem radialTestCLM_apply (W : 𝓢(ℝ, ℂ)) : radialTestCLM W = radialTest W := by
  ext z
  rfl

def radialFourierCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ, ℂ)).comp radialTestCLM

@[simp] theorem radialFourierCLM_apply (W : 𝓢(ℝ, ℂ)) :
    radialFourierCLM W = 𝓕 (radialTest W) := by
  simp [radialFourierCLM]

theorem paperRadialFourier_eq_plane (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    paperRadialFourier W t =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (Real.sqrt t : ℂ)) := by
  rw [paperRadialFourier, paperFourier_eq_standard, radialFourierCLM_apply]
  rfl

theorem paperFrequency_sqrt_norm_sq (t : ℝ) (ht : 0 ≤ t) :
    ‖paperFrequency (Real.sqrt t : ℂ)‖ ^ 2 = (4 / 3 : ℝ) * t := by
  rw [paperFrequency_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht]

theorem paperRadialFourier_weighted_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
      (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
        (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ)
          (radialFourierCLM W) := by
  let ξ : ℂ := paperFrequency (Real.sqrt t : ℂ)
  have hn : ‖ξ‖ ^ 2 = (4 / 3 : ℝ) * t := paperFrequency_sqrt_norm_sq t ht
  have hscale : 0 ≤ (2 / Real.sqrt 3 : ℝ) := by positivity
  have hpow : (1 + t) ^ A ≤ (1 + ‖ξ‖) ^ (2 * A) := by
    have hbase : 1 + t ≤ (1 + ‖ξ‖) ^ 2 := by
      nlinarith [norm_nonneg ξ]
    calc
      (1 + t) ^ A ≤ ((1 + ‖ξ‖) ^ 2) ^ A := pow_le_pow_left₀ (by positivity) hbase A
      _ = _ := by rw [← pow_mul]
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2 * A, 0)) (k := 2 * A) (n := 0) le_rfl le_rfl (radialFourierCLM W) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  rw [paperRadialFourier_eq_plane, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  change (1 + t) ^ A * ((2 / Real.sqrt 3) * ‖radialFourierCLM W ξ‖) ≤ _
  calc
    _ = (2 / Real.sqrt 3) * ((1 + t) ^ A * ‖radialFourierCLM W ξ‖) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((1 + ‖ξ‖) ^ (2 * A) * ‖radialFourierCLM W ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hscale
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hb hscale using 1
      ring_nf
      rfl

theorem schwartzCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem paperRadialFourier_source_weighted_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_finite_seminorm_control radialFourierCLM (Finset.Iic (2 * A, 0))
  refine ⟨s, (2 / Real.sqrt 3) * 2 ^ (2 * A) * C, by positivity, ?_⟩
  intro W t ht
  apply (paperRadialFourier_weighted_bound W A t ht).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W)
      (show 0 ≤ (2 / Real.sqrt 3) * 2 ^ (2 * A) by positivity)

theorem paperRadialFourier_source_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        ‖paperRadialFourier W t‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + t) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_source_weighted_bound A
  refine ⟨s, C, hC, ?_⟩
  intro W t ht
  apply (le_div_iff₀ (by positivity : 0 < (1 + t) ^ A)).mpr
  simpa only [mul_comm] using hbound W t ht

end

section
open MeasureTheory
open scoped SchwartzMap ContDiff

def halfEulerCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((x / 2 : ℝ) : ℂ))).comp
    (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem halfEulerCLM_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfEulerCLM g s = (s / 2 : ℝ) • deriv g s := by
  have hg : (fun x : ℝ => ((x / 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  simp only [halfEulerCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.derivCLM_apply]
  rfl

theorem hasDerivAt_halfFlow (g : 𝓢(ℝ, ℂ)) (a t : ℝ) :
    HasDerivAt (fun y : ℝ => g (a * Real.exp (y / 2)))
      (halfEulerCLM g (a * Real.exp (t / 2))) t := by
  have hf : HasDerivAt (fun y : ℝ => a * Real.exp (y / 2))
      ((a * Real.exp (t / 2)) / 2) t := by
    convert (((hasDerivAt_id t).div_const 2).exp.const_mul a) using 1 <;> simp only [id_eq] ; ring
  simpa only [halfEulerCLM_apply, Function.comp_def] using
    (g.hasDerivAt (a * Real.exp (t / 2))).scomp t hf

theorem iteratedDeriv_halfFlow (g : 𝓢(ℝ, ℂ)) (a : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun y : ℝ => g (a * Real.exp (y / 2))) t =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (a * Real.exp (t / 2)) := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => g (a * Real.exp (y / 2))) =
        fun y : ℝ => halfEulerCLM g (a * Real.exp (y / 2)) :=
      funext (fun y => (hasDerivAt_halfFlow g a y).deriv)
    rw [hd, ih (halfEulerCLM g),
      Function.iterate_succ_apply]

 theorem sqrt_exp_half (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  rw [Real.sqrt_eq_iff_eq_sq (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

 theorem eulerDeriv_sqrt_profile (g : 𝓢(ℝ, ℂ)) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (Real.sqrt x) := by
  unfold LocalLogFourier.eulerDeriv
  have hflow : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [hflow, iteratedDeriv_halfFlow]
  simp

theorem contDiffOn_sqrt_profile (g : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ => g (Real.sqrt x)) (Set.Ioi 0) := by
  intro x hx
  exact ((g.smooth ⊤).contDiffAt.comp x
    (Real.contDiffAt_sqrt (ne_of_gt hx))).contDiffWithinAt

theorem contDiff_sqrt_profile_log (g : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) := by
  have heq : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [heq]
  exact (g.smooth ⊤).comp (by fun_prop)

theorem sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖g (Real.sqrt x)‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ (2 * A) 0 g) := by
  have hsmall := SchwartzMap.norm_le_seminorm ℝ g (Real.sqrt x)
  have hlarge := SchwartzMap.norm_pow_mul_le_seminorm ℝ g (2 * A) (Real.sqrt x)
  have hsqrt : ‖Real.sqrt x‖ ^ (2 * A) = x ^ A := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      pow_mul, Real.sq_sqrt hx]
  rw [hsqrt] at hlarge
  have hs0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := by positivity
  have hsA : 0 ≤ SchwartzMap.seminorm ℝ (2 * A) 0 g := by positivity
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      _ ≤ 2 ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ 0 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hp : (1 + x) ^ A ≤ (2 * x) ^ A := by gcongr; linarith
    calc
      _ ≤ (2 * x) ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2 ^ A * (x ^ A * ‖g (Real.sqrt x)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ (2 * A) 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith

theorem eulerDeriv_sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) +
        SchwartzMap.seminorm ℝ (2 * A) 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g)) := by
  rw [eulerDeriv_sqrt_profile g j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem paperFrequency_real_temperate :
    (fun s : ℝ => paperFrequency (s : ℂ)).HasTemperateGrowth := by
  have heq : (fun s : ℝ => paperFrequency (s : ℂ)) =
      fun s : ℝ => (2 * Complex.I / (Real.sqrt 3 : ℂ)) * (s : ℂ) := by
    funext s
    simp [paperFrequency]
  rw [heq]
  fun_prop

theorem paperFrequency_real_growth (s : ℝ) :
    ‖s‖ ≤ 1 + ‖paperFrequency (s : ℂ)‖ := by
  have hn := paperFrequency_norm_sq (s : ℂ)
  have heq : ‖(s : ℂ)‖ = ‖s‖ := by simp
  rw [heq] at hn
  have hns := norm_nonneg s
  have hnf := norm_nonneg (paperFrequency (s : ℂ))
  nlinarith [sq_nonneg (‖s‖ - ‖paperFrequency (s : ℂ)‖)]

def paperRealRayCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ paperFrequency_real_temperate
    ⟨1, 1, by simpa using paperFrequency_real_growth⟩

@[simp] theorem paperRealRayCLM_apply (g : 𝓢(ℂ, ℂ)) (s : ℝ) :
    paperRealRayCLM g s = g (paperFrequency (s : ℂ)) := rfl

def halfEulerIterateCLM : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (halfEulerCLM.restrictScalars ℝ).comp (halfEulerIterateCLM j)

@[simp] theorem halfEulerIterateCLM_apply (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    halfEulerIterateCLM j g = (halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [halfEulerIterateCLM, ContinuousLinearMap.comp_apply,
      ih, Function.iterate_succ_apply']
    rfl

def paperFourierRayCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) • (paperRealRayCLM.comp radialFourierCLM)

@[simp] theorem paperFourierRayCLM_apply (W : 𝓢(ℝ, ℂ)) (s : ℝ) :
    paperFourierRayCLM W s =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (s : ℂ)) := by
  simp [paperFourierRayCLM]

theorem paperRadialFourier_eq_ray (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier W = fun x : ℝ => paperFourierRayCLM W (Real.sqrt x) := by
  funext x
  rw [paperRadialFourier_eq_plane, paperFourierRayCLM_apply]

def paperEulerCLM (j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp paperFourierRayCLM

theorem paperRadialFourier_eulerDeriv (W : 𝓢(ℝ, ℂ)) (j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (paperRadialFourier W) j x =
      paperEulerCLM j W (Real.sqrt x) := by
  rw [paperRadialFourier_eq_ray, eulerDeriv_sqrt_profile _ j x hx]
  simp only [paperEulerCLM, ContinuousLinearMap.comp_apply, halfEulerIterateCLM_apply]

theorem paperRadialFourier_contDiffOn (W : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiffOn_sqrt_profile _

theorem paperRadialFourier_log_contDiff (W : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => paperRadialFourier W (x * Real.exp t)) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiff_sqrt_profile_log _ x hx

theorem paperRadialFourier_euler_weighted_bound (W : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 (paperEulerCLM j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (paperEulerCLM j W)) := by
  rw [paperRadialFourier_eulerDeriv W j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem schwartzCLM_family_finite_seminorm_control
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let qj : ℕ → Seminorm ℝ 𝓢(ℝ, ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ 0 0 + SchwartzMap.seminorm ℝ (2 * A) 0).comp
      (T j).toLinearMap
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := ∑ j ∈ Finset.range (K + 1), qj j
  have hqfun : (q : 𝓢(ℝ, ℂ) → ℝ) = fun W => ∑ j ∈ Finset.range (K + 1),
      (SchwartzMap.seminorm ℝ 0 0 (T j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T j W)) := by
    funext W
    simp [q, qj]
  have hq : Continuous q := by
    rw [hqfun]
    apply continuous_finsetSum
    intro j hj
    exact (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
        (T j).continuous).add
      (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2 * A, 0)).comp
        (T j).continuous)
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W j hj
    apply le_trans ?_ (Seminorm.le_def.mp hbound W)
    rw [hqfun]
    exact Finset.single_le_sum (f := fun i =>
      SchwartzMap.seminorm ℝ 0 0 (T i W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T i W))
      (by intro i hi; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem paperRadialFourier_euler_source_weighted_bound (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_family_finite_seminorm_control paperEulerCLM A K
  refine ⟨s, 2 ^ A * C, by positivity, ?_⟩
  intro W j hj x hx
  apply (paperRadialFourier_euler_weighted_bound W A j x hx).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W j hj) (show 0 ≤ (2 : ℝ) ^ A by positivity)

theorem paperRadialFourier_euler_source_decay (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + x) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨s, C, hC, ?_⟩
  intro W j hj x hx
  apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ A)).mpr
  simpa only [mul_comm] using hbound W j hj x hx

theorem paperRadialFourier_euler_bound (W : 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro j hj x hx
  exact hbound W j hj x hx.le

theorem compact_paperRadialFourier_regular
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  exact ⟨paperRadialFourier_contDiffOn (hWc.toSchwartzMap hWs),
    paperRadialFourier_euler_bound (hWc.toSchwartzMap hWs) A K⟩

theorem paperRadialFourier_log_separation
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_uniform V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem inverse_square_le_cauchy_product (a b q : ℝ) (hq : 0 ≤ q)
    (hQ : (a ^ 2 + b ^ 2) / 2 ≤ q) :
    ((1 + q) ^ 2)⁻¹ ≤
      4 * ((1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) := by
  have hsum : 1 + a ^ 2 + b ^ 2 ≤ 2 * (1 + q) := by linarith
  have hsquare : (1 + a ^ 2 + b ^ 2) ^ 2 ≤ (2 * (1 + q)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  have hden : (1 + a ^ 2) * (1 + b ^ 2) ≤ 4 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  calc
    _ = 1 / (1 + q) ^ 2 := by simp only [one_div]
    _ ≤ 4 / ((1 + a ^ 2) * (1 + b ^ 2)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem eisenstein_cauchy_summable :
    Summable (fun h : O => ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => inv_nonneg.mpr (sq_nonneg _)) _
    (summable_int_cauchy_product.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (p.1 : ℝ) (p.2 : ℝ)
    (‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (sq_nonneg _)
  change ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 2 ≤
    ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ))]

def eisensteinCauchyMass : ℝ :=
  ∑' h : O, ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹

theorem eisensteinCauchyMass_nonneg : 0 ≤ eisensteinCauchyMass :=
  tsum_nonneg (fun _ => by positivity)

theorem eisensteinCauchyMass_subtype (S : Set O) :
    (∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤ eisensteinCauchyMass := by
  exact (eisenstein_cauchy_summable.subtype S).tsum_le_tsum_of_inj
    Subtype.val Subtype.val_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    eisenstein_cauchy_summable

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_injective_on_squarefree
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : idealSupport F I = idealSupport F J) : I = J := by
  have hfac : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors J := by
    rw [Multiset.Nodup.ext
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsI.ne_zero).mp hsI)
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsJ.ne_zero).mp hsJ)]
    intro P
    constructor
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
      have hp : p ∈ idealSupport F I := (mem_idealSupport_iff F I p).mpr hP
      rw [h] at hp
      exact (mem_idealSupport_iff F J p).mp hp
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨J, hJ, hP⟩⟩
      have hp : p ∈ idealSupport F J := (mem_idealSupport_iff F J p).mpr hP
      rw [← h] at hp
      exact (mem_idealSupport_iff F I p).mp hp
  rw [← Ideal.prod_normalizedFactors_eq_self hsI.ne_zero,
    ← Ideal.prod_normalizedFactors_eq_self hsJ.ne_zero, hfac]

theorem baseChangeWeight_eq_zero_of_not_squarefree
    {q : ℕ} (χ : DirichletCharacter ℂ q) {I : Ideal O} (hI : ¬ Squarefree I) :
    baseChangeWeight χ I = 0 := by
  simp only [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

end ConcretePrimeRowBridge

end

end OAI
