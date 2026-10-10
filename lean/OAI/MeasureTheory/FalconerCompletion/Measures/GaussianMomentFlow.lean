import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAxisIntegral

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set Filter
open scoped SchwartzMap FourierTransform Topology ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def gaussianMomentFlowND (φ : 𝓢(V,ℂ)) (k : ℕ) (t : ℝ) : ℂ :=
  ∫ x : V, Complex.exp (Complex.I*(t*‖x‖^2 : ℝ)) * (‖x‖:ℂ)^(2*k) * φ x

lemma gaussianMomentFlowND_integrable (φ : 𝓢(V,ℂ)) (k : ℕ) (t : ℝ) :
    Integrable (fun x : V => Complex.exp (Complex.I*(t*‖x‖^2 : ℝ)) *
      (‖x‖:ℂ)^(2*k) * φ x) := by
  apply (φ.integrable_pow_mul volume (2*k)).mono' (by fun_prop)
  filter_upwards [] with x
  simp only [norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_norm]
  rfl

lemma gaussianMomentFlowND_hasDerivAt (φ : 𝓢(V,ℂ)) (k : ℕ) (t : ℝ) :
    HasDerivAt (gaussianMomentFlowND φ k) (Complex.I*gaussianMomentFlowND φ (k+1) t) t := by
  let F (s : ℝ) (x : V) := Complex.exp (Complex.I*(s*‖x‖^2 : ℝ)) * (‖x‖:ℂ)^(2*k) * φ x
  let F' (s : ℝ) (x : V) := Complex.I *
    (Complex.exp (Complex.I*(s*‖x‖^2 : ℝ)) * (‖x‖:ℂ)^(2*(k+1)) * φ x)
  have hF (s : ℝ) : Continuous (F s) := by unfold F; fun_prop
  have hF' (s : ℝ) : Continuous (F' s) := by unfold F'; fun_prop
  have hd (s : ℝ) (x : V) : HasDerivAt (fun s => F s x) (F' s x) s := by
    have h := (((((hasDerivAt_id s).mul_const (‖x‖^2)).ofReal_comp.const_mul Complex.I).cexp
      ).mul_const ((‖x‖:ℂ)^(2*k))).mul_const (φ x)
    dsimp only [F,F']
    convert h using 1 <;> try rfl
    simp only [id_eq] at *
    push_cast
    rw [Nat.mul_add,pow_add]
    ring
  have hbound : ∀ᵐ x : V, ∀ s ∈ (univ : Set ℝ),
      ‖F' s x‖ ≤ ‖x‖^(2*(k+1))*‖φ x‖ := by
    filter_upwards [] with x s _
    simp only [F',norm_mul,Complex.norm_I,one_mul,Complex.norm_exp_I_mul_ofReal,
      norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_norm,le_refl]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := t) (F := F) (F' := F') (bound := fun x => ‖x‖^(2*(k+1))*‖φ x‖)
    Filter.univ_mem (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    (gaussianMomentFlowND_integrable φ k t) (hF' t).aestronglyMeasurable hbound
    (φ.integrable_pow_mul volume (2*(k+1)))
    (Filter.Eventually.of_forall (fun x s _ => hd s x))
  unfold gaussianMomentFlowND
  simpa only [F,F',integral_const_mul] using h.2

lemma gaussianMomentFlowND_deriv (φ : 𝓢(V,ℂ)) (k : ℕ) :
    deriv (gaussianMomentFlowND φ k) = fun t => Complex.I*gaussianMomentFlowND φ (k+1) t := by
  funext t
  exact (gaussianMomentFlowND_hasDerivAt φ k t).deriv

lemma gaussianMomentFlowND_contDiff (φ : 𝓢(V,ℂ)) (k : ℕ) :
    ContDiff ℝ ∞ (gaussianMomentFlowND φ k) := by
  rw [contDiff_infty]
  intro m
  induction m generalizing k with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun t => (gaussianMomentFlowND_hasDerivAt φ k t).continuousAt))
  | succ m ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun t => (gaussianMomentFlowND_hasDerivAt φ k t).differentiableAt, ?_⟩
    refine ⟨by simp,?_⟩
    rw [gaussianMomentFlowND_deriv]
    exact contDiff_const.mul (ih (k+1))

lemma gaussianMomentFlowND_iteratedDeriv (φ : 𝓢(V,ℂ)) (k j : ℕ) :
    iteratedDeriv j (gaussianMomentFlowND φ k) =
      fun t => Complex.I^j*gaussianMomentFlowND φ (k+j) t := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [deriv_const_mul _ ((gaussianMomentFlowND_hasDerivAt φ (k+j) t).differentiableAt),
      (gaussianMomentFlowND_hasDerivAt φ (k+j) t).deriv]
    simp only [pow_succ,Nat.add_assoc,mul_assoc]

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
