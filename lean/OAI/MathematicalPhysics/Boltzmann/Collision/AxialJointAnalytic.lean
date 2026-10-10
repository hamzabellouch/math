import OAI.MathematicalPhysics.Boltzmann.Branching.TriangularLinearMap
import OAI.MathematicalPhysics.Boltzmann.Collision.AnalyticTools
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace OAI

section

/-! # Spatial derivatives of the implicit cold-jet flow -/

noncomputable section

open Filter
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialDerivative

def A (α γ s z : ℝ) : ℝ := (α * γ / s) * S (γ * z / s)

theorem A_nonneg {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (z : ℝ) :
    0 ≤ A α γ s z := mul_nonneg (div_nonneg (mul_nonneg hα hγ) hs) (S_pos _).le

theorem profile_derivative (σ α γ s z : ℝ) :
    HasDerivAt (profile σ α γ s) (A α γ s z) z := by
  have h := (tanh_derivative (γ * z / s)).comp z (((hasDerivAt_id z).const_mul γ).div_const s)
  convert (hasDerivAt_const z σ).add (h.const_mul α) using 1
  · funext x
    rfl
  · unfold A
    ring

theorem characteristic_derivative (σ α γ s t z : ℝ) :
    HasDerivAt (characteristic σ α γ s t) (1 + t * A α γ s z) z :=
  (hasDerivAt_id z).add ((profile_derivative σ α γ s z).const_mul t)

theorem foot_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) :
    HasDerivAt (foot σ α γ s t) (1 + t * A α γ s (foot σ α γ s t z))⁻¹ z := by
  apply HasDerivAt.of_local_left_inverse
    (foot_lipschitzWith hα hγ hs ht).continuous.continuousAt
    (characteristic_derivative σ α γ s t (foot σ α γ s t z))
  · have hA := A_nonneg hα hγ hs.le (foot σ α γ s t z)
    positivity
  · exact Eventually.of_forall (fun y => characteristic_foot hα)

theorem velocity_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) :
    HasDerivAt (velocity σ α γ s t)
      (A α γ s (foot σ α γ s t z) / (1 + t * A α γ s (foot σ α γ s t z))) z := by
  have h := (profile_derivative σ α γ s (foot σ α γ s t z)).comp z
    (foot_derivative hα hγ hs ht z)
  have he : profile σ α γ s ∘ foot σ α γ s t = velocity σ α γ s t :=
    funext (fun _ => (velocity_spec hα).symm)
  rw [he] at h
  simpa only [div_eq_mul_inv] using h

theorem velocity_derivative_nonneg {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) : 0 ≤ deriv (velocity σ α γ s t) z := by
  rw [(velocity_derivative hα hγ hs ht z).deriv]
  exact div_nonneg (A_nonneg hα hγ hs.le _) (by
    have := A_nonneg hα hγ hs.le (foot σ α γ s t z)
    positivity)

end BoltzmannNonuniqueness.AxialDerivative

end

end

section

/-! # Continuity of the implicit axial flow along free transport -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialTransport

def flightFoot (σ α γ s z v t : ℝ) : ℝ := foot σ α γ s t (z + t * v)

def flightVelocity (σ α γ s z v t : ℝ) : ℝ := velocity σ α γ s t (z + t * v)

theorem velocity_abs_le {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    |velocity σ α γ s t z| ≤ |σ| + α := by
  have h := velocity_sub_center_le (σ := σ) (γ := γ) (s := s) (t := t) (z := z) hα
  have htri := abs_add_le (velocity σ α γ s t z - σ) σ
  rw [sub_add_cancel] at htri
  linarith

theorem flightFoot_distance {σ α γ s t₀ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht₀ : 0 ≤ t₀) (z v t : ℝ) :
    |flightFoot σ α γ s z v t - flightFoot σ α γ s z v t₀| ≤
      |t - t₀| * (|v| + |σ| + α) := by
  have hi := characteristic_inverse_lipschitz (σ := σ) (t := t₀)
    (x := flightFoot σ α γ s z v t) (y := flightFoot σ α γ s z v t₀) hα hγ hs ht₀
  have he : characteristic σ α γ s t₀ (flightFoot σ α γ s z v t) =
      z + t * v + (t₀ - t) * flightVelocity σ α γ s z v t := by
    unfold characteristic flightFoot flightVelocity foot
    rw [← velocity_spec hα]
    ring
  have he₀ : characteristic σ α γ s t₀ (flightFoot σ α γ s z v t₀) = z + t₀ * v :=
    characteristic_foot hα
  rw [he, he₀] at hi
  have he' : z + t * v + (t₀ - t) * flightVelocity σ α γ s z v t - (z + t₀ * v) =
      (t - t₀) * (v - flightVelocity σ α γ s z v t) := by ring
  rw [he', abs_mul] at hi
  have hu := velocity_abs_le (σ := σ) (γ := γ) (s := s) (t := t) (z := z + t * v) hα
  change |flightVelocity σ α γ s z v t| ≤ |σ| + α at hu
  have htri := abs_sub v (flightVelocity σ α γ s z v t)
  exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))

theorem flightFoot_continuousAt {σ α γ s t₀ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht₀ : 0 ≤ t₀) (z v : ℝ) :
    ContinuousAt (flightFoot σ α γ s z v) t₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hC : 0 ≤ |v| + |σ| + α := by positivity
  refine ⟨ε / (|v| + |σ| + α + 1), div_pos hε (by positivity), ?_⟩
  intro t ht
  rw [Real.dist_eq] at ht ⊢
  apply (flightFoot_distance hα hγ hs ht₀ z v t).trans_lt
  calc
    |t - t₀| * (|v| + |σ| + α) ≤ |t - t₀| * (|v| + |σ| + α + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ < ε := (lt_div_iff₀ (by positivity)).mp ht

end BoltzmannNonuniqueness.AxialTransport

end

end

section

/-! # Differentiation of the cold-jet flow along free flights -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.AxialTransport

namespace BoltzmannNonuniqueness.AxialFlightDerivative

private theorem time_mul_derivative {g : ℝ → ℝ} {t₀ : ℝ} (hg : ContinuousAt g t₀) :
    HasDerivAt (fun t => (t - t₀) * g t) (g t₀) t₀ := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have he : slope (fun t => (t - t₀) * g t) t₀ =ᶠ[𝓝[≠] t₀] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t - t₀ ≠ 0 := sub_ne_zero.mpr ht
    rw [slope_def_field]
    simp only [sub_self, zero_mul, sub_zero]
    exact mul_div_cancel_left₀ (g t) hne
  exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

theorem flightFoot_derivative {σ α γ s t₀ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht₀ : 0 ≤ t₀) (z v : ℝ) :
    HasDerivAt (flightFoot σ α γ s z v)
      ((v - flightVelocity σ α γ s z v t₀) /
        (1 + t₀ * A α γ s (flightFoot σ α γ s z v t₀))) t₀ := by
  have hg := flightFoot_continuousAt (σ := σ) hα hγ hs ht₀ z v
  have hp := (continuous_profile σ α γ s).continuousAt.comp hg
  have hprod := time_mul_derivative hp
  have hZ : HasDerivAt (fun t : ℝ => z + t * v) v t₀ := by
    convert (hasDerivAt_const t₀ z).add ((hasDerivAt_id t₀).mul_const v) using 1
    · funext t
      rfl
    · ring
  have hH := hZ.sub hprod
  have he : characteristic σ α γ s t₀ ∘ flightFoot σ α γ s z v =
      fun t => z + t * v - (t - t₀) * profile σ α γ s (flightFoot σ α γ s z v t) := by
    funext t
    have hc : characteristic σ α γ s t (flightFoot σ α γ s z v t) = z + t * v :=
      characteristic_foot hα
    dsimp only [Function.comp_apply, characteristic] at hc ⊢
    nlinarith only [hc]
  have hne : 1 + t₀ * A α γ s (flightFoot σ α γ s z v t₀) ≠ 0 := by
    have := A_nonneg hα hγ hs.le (flightFoot σ α γ s z v t₀)
    positivity
  have h := (characteristic_derivative σ α γ s t₀ (flightFoot σ α γ s z v t₀)).of_comp_left
    hg hH hne (Filter.Eventually.of_forall (fun t => congrFun he t))
  have hv : profile σ α γ s (flightFoot σ α γ s z v t₀) = flightVelocity σ α γ s z v t₀ :=
    (velocity_spec hα).symm
  simpa only [Function.comp_apply, hv] using h

theorem flightVelocity_derivative {σ α γ s t₀ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht₀ : 0 ≤ t₀) (z v : ℝ) :
    HasDerivAt (flightVelocity σ α γ s z v)
      ((v - flightVelocity σ α γ s z v t₀) *
        (A α γ s (flightFoot σ α γ s z v t₀) /
          (1 + t₀ * A α γ s (flightFoot σ α γ s z v t₀)))) t₀ := by
  have h := (profile_derivative σ α γ s (flightFoot σ α γ s z v t₀)).comp t₀
    (flightFoot_derivative hα hγ hs ht₀ z v)
  have he : profile σ α γ s ∘ flightFoot σ α γ s z v = flightVelocity σ α γ s z v :=
    funext (fun _ => (velocity_spec hα).symm)
  rw [he] at h
  convert h using 1
  ring

end BoltzmannNonuniqueness.AxialFlightDerivative

end

end

section

/-! # Joint time and position continuity of the implicit axial flow -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AxialFlow

theorem foot_time_space_bound {σ α γ s t₀ z₀ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₀ : 0 ≤ t₀) (t z : ℝ) :
    |foot σ α γ s t z-foot σ α γ s t₀ z₀| ≤
      |t-t₀| *(|σ|+α)+|z-z₀| := by
  have htime := AxialTransport.flightFoot_distance (σ := σ) hα hγ hs ht₀ z 0 t
  simp only [AxialTransport.flightFoot,zero_add,abs_zero,add_zero,mul_zero] at htime
  have hspace := foot_lipschitz (σ := σ) (z := z) (w := z₀) hα hγ hs ht₀
  calc
    _ ≤ |foot σ α γ s t z-foot σ α γ s t₀ z|+
        |foot σ α γ s t₀ z-foot σ α γ s t₀ z₀| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add htime hspace

theorem foot_joint_continuousAt {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    ContinuousAt (fun p : ℝ × ℝ => foot σ α γ s p.1 p.2) (t,z) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ p : ℝ × ℝ,
      0 ≤ dist (foot σ α γ s p.1 p.2) (foot σ α γ s t z) := fun _ => dist_nonneg
  have hu (p : ℝ × ℝ) :
      dist (foot σ α γ s p.1 p.2) (foot σ α γ s t z) ≤
        |p.1-t| *(|σ|+α)+|p.2-z| := by
    simpa only [Real.dist_eq] using foot_time_space_bound hα hγ hs ht p.1 p.2
  apply squeeze_zero hb hu
  have h₁ := ((continuous_fst.tendsto (t,z)).sub_const t).abs.mul_const (|σ|+α)
  have h₂ := ((continuous_snd.tendsto (t,z)).sub_const z).abs
  simpa only [sub_self,abs_zero,zero_mul,zero_add] using h₁.add h₂

theorem clamped_foot_continuous {σ α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Continuous (fun p : ℝ × ℝ => foot σ α γ s (max 0 p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hg : ContinuousAt (fun u : ℝ × ℝ => (max 0 u.1,u.2)) p :=
    ((continuous_const.max continuous_fst).prodMk continuous_snd).continuousAt
  have hh : Tendsto (fun u : ℝ × ℝ => foot σ α γ s u.1 u.2)
      (𝓝 (max 0 p.1,p.2)) (𝓝 (foot σ α γ s (max 0 p.1) p.2)) :=
    foot_joint_continuousAt hα hγ hs (le_max_left 0 p.1)
  exact Tendsto.comp hh hg

theorem clamped_velocity_continuous {σ α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Continuous (fun p : ℝ × ℝ => velocity σ α γ s (max 0 p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => velocity σ α γ s (max 0 p.1) p.2) =
      profile σ α γ s ∘ (fun p : ℝ × ℝ => foot σ α γ s (max 0 p.1) p.2) := by
    funext p
    exact velocity_spec hα
  rw [he]
  exact (continuous_profile σ α γ s).comp (clamped_foot_continuous hα hγ hs)

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-! # Analyticity of the explicit cold profile and characteristic maps -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialAnalytic

theorem tanh_analytic (x : ℝ) : AnalyticAt ℝ Real.tanh x := by
  have he : Real.tanh = Real.sinh / Real.cosh :=
    funext (fun y => Real.tanh_eq_sinh_div_cosh y)
  rw [he]
  exact Real.analyticAt_sinh.div Real.analyticAt_cosh (Real.cosh_pos x).ne'

theorem profile_analytic (σ α γ s x : ℝ) : AnalyticAt ℝ (profile σ α γ s) x := by
  have harg : AnalyticAt ℝ (fun z : ℝ => γ*z/s) x := by fun_prop
  have h := (tanh_analytic (γ*x/s)).comp (f := fun z : ℝ => γ*z/s) harg
  change AnalyticAt ℝ (fun z => σ+α*(Real.tanh ∘ (fun y : ℝ => γ*y/s)) z) x
  exact analyticAt_const.add (analyticAt_const.mul h)

theorem characteristic_analytic (σ α γ s t x : ℝ) :
    AnalyticAt ℝ (characteristic σ α γ s t) x :=
  analyticAt_id.add (analyticAt_const.mul (profile_analytic σ α γ s x))

theorem foot_analytic {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) : AnalyticAt ℝ (foot σ α γ s t) z := by
  let a := foot σ α γ s t z
  have hf := characteristic_analytic σ α γ s t a
  have hd : deriv (characteristic σ α γ s t) a ≠ 0 := by
    rw [(characteristic_derivative σ α γ s t a).deriv]
    have hA := A_nonneg hα hγ hs.le a
    positivity
  have hi := AnalyticInverse.analytic_of_eventually_left_inverse _ hf
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
    (Eventually.of_forall (fun y => foot_characteristic hα hγ hs ht (z := y)))
  simpa only [a,characteristic_foot hα] using hi

theorem velocity_analytic {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) : AnalyticAt ℝ (velocity σ α γ s t) z := by
  have h := (profile_analytic σ α γ s (foot σ α γ s t z)).comp
    (foot_analytic hα hγ hs ht z)
  have he : (fun y => profile σ α γ s (foot σ α γ s t y)) = velocity σ α γ s t :=
    funext (fun _ => (velocity_spec hα).symm)
  change AnalyticAt ℝ (fun y => profile σ α γ s (foot σ α γ s t y)) z at h
  rwa [he] at h

end BoltzmannNonuniqueness.AxialAnalytic

end

end

section

/-! # Joint analyticity of the cold flow in scale, time, and position -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialAnalytic

abbrev FlowParameters := (ℝ × ℝ) × ℝ

def jointCharacteristic (σ α γ : ℝ) (p : FlowParameters) : FlowParameters :=
  (p.1, characteristic σ α γ p.1.1 p.1.2 p.2)

def jointFoot (σ α γ : ℝ) (p : FlowParameters) : FlowParameters :=
  (p.1, foot σ α γ p.1.1 p.1.2 p.2)

theorem jointProfile_analytic (σ α γ : ℝ) (p : FlowParameters) (hs : p.1.1 ≠ 0) :
    AnalyticAt ℝ (fun q : FlowParameters => profile σ α γ q.1.1 q.2) p := by
  have hscale : AnalyticAt ℝ (fun q : FlowParameters => q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have harg : AnalyticAt ℝ (fun q : FlowParameters => γ*q.2/q.1.1) p :=
    (analyticAt_const.mul analyticAt_snd).div hscale hs
  have htan := (tanh_analytic (γ*p.2/p.1.1)).comp
    (f := fun q : FlowParameters => γ*q.2/q.1.1) harg
  exact analyticAt_const.add (analyticAt_const.mul htan)

theorem jointCharacteristic_analytic (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) : AnalyticAt ℝ (jointCharacteristic σ α γ) p := by
  have ht : AnalyticAt ℝ (fun q : FlowParameters => q.1.2) p :=
    analyticAt_snd.comp analyticAt_fst
  exact analyticAt_fst.prod
    (analyticAt_snd.add (ht.mul (jointProfile_analytic σ α γ p hs)))

theorem jointCharacteristic_derivative_fst (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) (v : FlowParameters) :
    (fderiv ℝ (jointCharacteristic σ α γ) p v).1 = v.1 := by
  have hd := (jointCharacteristic_analytic σ α γ p hs).hasStrictFDerivAt.hasFDerivAt
  have he := hd.fst.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  exact congrArg (fun L : FlowParameters →L[ℝ] ℝ × ℝ => L v) he

theorem jointCharacteristic_derivative_vertical (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) :
    (fderiv ℝ (jointCharacteristic σ α γ) p (0,1)).2 =
      1+p.1.2*A α γ p.1.1 p.2 := by
  have hd := (jointCharacteristic_analytic σ α γ p hs).hasStrictFDerivAt.hasFDerivAt
  have hline : HasDerivAt (fun z : ℝ => (p.1,z)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h := hd.snd.comp_hasDerivAt p.2 hline
  exact h.unique (characteristic_derivative σ α γ p.1.1 p.1.2 p.2)

theorem jointFoot_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (p : FlowParameters) (hs : 0 < p.1.1) (ht : 0 < p.1.2) :
    AnalyticAt ℝ (jointFoot σ α γ) p := by
  let a := jointFoot σ α γ p
  have ha : a.1 = p.1 := rfl
  have hf := jointCharacteristic_analytic σ α γ a hs.ne'
  have hd : (fderiv ℝ (jointCharacteristic σ α γ) a (0,1)).2 ≠ 0 := by
    rw [jointCharacteristic_derivative_vertical σ α γ a hs.ne']
    have hA := A_nonneg hα hγ hs.le a.2
    change 1+p.1.2*A α γ p.1.1 a.2 ≠ 0
    positivity
  let e := triangularEquiv (fderiv ℝ (jointCharacteristic σ α γ) a)
    (jointCharacteristic_derivative_fst σ α γ a hs.ne') hd
  have hleft : ∀ᶠ q in 𝓝 a, jointFoot σ α γ (jointCharacteristic σ α γ q) = q := by
    have hS : ∀ᶠ q : FlowParameters in 𝓝 a, 0 < q.1.1 :=
      (show ContinuousAt (fun q : FlowParameters => q.1.1) a by fun_prop).eventually
        (lt_mem_nhds hs)
    have hT : ∀ᶠ q : FlowParameters in 𝓝 a, 0 < q.1.2 :=
      (show ContinuousAt (fun q : FlowParameters => q.1.2) a by fun_prop).eventually
        (lt_mem_nhds ht)
    filter_upwards [hS,hT] with q hqS hqT
    refine Prod.ext rfl ?_
    exact foot_characteristic hα hγ hqS hqT.le
  have hi := AnalyticInverse.analytic_of_eventually_left_inverse e hf
    (by simpa only [e,triangularEquiv_coe] using hf.hasStrictFDerivAt) hleft
  have he : jointCharacteristic σ α γ a = p := by
    refine Prod.ext ha ?_
    exact characteristic_foot hα
  rwa [he] at hi

theorem jointVelocity_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (p : FlowParameters) (hs : 0 < p.1.1) (ht : 0 < p.1.2) :
    AnalyticAt ℝ (fun q : FlowParameters => velocity σ α γ q.1.1 q.1.2 q.2) p := by
  have h := (jointProfile_analytic σ α γ (jointFoot σ α γ p) hs.ne').comp
    (jointFoot_analytic hα hγ p hs ht)
  change AnalyticAt ℝ (fun q : FlowParameters =>
    profile σ α γ q.1.1 (foot σ α γ q.1.1 q.1.2 q.2)) p at h
  have he : (fun q : FlowParameters => profile σ α γ q.1.1
      (foot σ α γ q.1.1 q.1.2 q.2)) =
      (fun q : FlowParameters => velocity σ α γ q.1.1 q.1.2 q.2) :=
    funext (fun _ => (velocity_spec hα).symm)
  rwa [he] at h

end BoltzmannNonuniqueness.AxialAnalytic

end

end

end OAI
