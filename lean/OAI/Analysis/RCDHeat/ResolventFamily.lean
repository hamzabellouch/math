import Mathlib
import OAI.Analysis.RCDHeat.Density

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: ResolventFamily, Yosida, BoundedSemigroup. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section ResolventFamily
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_sub_left (f g h : SobolevSpace μ hQ) :
    energyForm μ hQ (f - g) h = energyForm μ hQ f h - energyForm μ hQ g h := by
  simp only [energyForm, map_sub, inner_sub_left]
  ring

 
noncomputable def resolventLp (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (SobolevSpace.toLpCLM μ hQ).comp (SobolevSpace.resolventAt μ hQ t ht)

 theorem resolventLp_apply (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    resolventLp μ hQ t ht f =
      SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f) := rfl

 theorem resolventLp_norm_le (t : ℝ) (ht : 0 < t) : ‖resolventLp μ hQ t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul, resolventLp_apply] using SobolevSpace.resolventAt_norm_le μ hQ t ht f

 theorem resolventLp_inner (t : ℝ) (ht : 0 < t) (f g : Lp ℝ 2 μ) :
    inner ℝ (resolventLp μ hQ t ht f) g = inner ℝ f (resolventLp μ hQ t ht g) := by
  have hfg := SobolevSpace.resolventAt_equation μ hQ t ht f
    (SobolevSpace.resolventAt μ hQ t ht g)
  have hgf := SobolevSpace.resolventAt_equation μ hQ t ht g
    (SobolevSpace.resolventAt μ hQ t ht f)
  rw [energyForm_comm μ hQ (SobolevSpace.resolventAt μ hQ t ht g),
    real_inner_comm (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f))
      (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht g)),
    real_inner_comm (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f)) g] at hgf
  change inner ℝ (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht f)) g = inner ℝ f (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ t ht g))
  linarith

 theorem resolventLp_selfAdjoint (t : ℝ) (ht : 0 < t) :
    IsSelfAdjoint (resolventLp μ hQ t ht) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (resolventLp_inner μ hQ t ht f g).symm

 theorem resolventLp_inner_nonneg (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (resolventLp μ hQ t ht f) := by
  have h := SobolevSpace.resolventAt_equation μ hQ t ht f
    (SobolevSpace.resolventAt μ hQ t ht f)
  rw [energyForm_self, real_inner_self_eq_norm_sq] at h
  rw [resolventLp_apply, ← h]
  exact add_nonneg (sq_nonneg _) (mul_nonneg ht.le
    (mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ _)))

 theorem resolventLp_sub_identity_inner_nonneg (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (f - resolventLp μ hQ t ht f) := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hi := real_inner_le_norm f (resolventLp μ hQ t ht f)
  have hn := mul_le_mul_of_nonneg_left (SobolevSpace.resolventAt_norm_le μ hQ t ht f)
    (norm_nonneg f)
  change ‖f‖ * ‖resolventLp μ hQ t ht f‖ ≤ ‖f‖ * ‖f‖ at hn
  nlinarith

 theorem SobolevSpace.resolventAt_identity (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℝ 2 μ) :
    s • SobolevSpace.resolventAt μ hQ s hs f - t • SobolevSpace.resolventAt μ hQ t ht f =
      (s - t) • SobolevSpace.resolventAt μ hQ t ht (resolventLp μ hQ s hs f) := by
  conv_rhs => rw [← map_smul]
  apply SobolevSpace.resolventAt_unique μ hQ ht
  intro φ
  simp only [map_sub, map_smul, inner_sub_left, real_inner_smul_left,
    energyForm_sub_left, energyForm_smul_left]
  have hs' := SobolevSpace.resolventAt_equation μ hQ s hs f φ
  have ht' := SobolevSpace.resolventAt_equation μ hQ t ht f φ
  change _ = (s - t) * inner ℝ
    (SobolevSpace.toLp μ hQ (SobolevSpace.resolventAt μ hQ s hs f)) (SobolevSpace.toLp μ hQ φ)
  have hs'' := congrArg (t * ·) hs'
  have ht'' := congrArg (t * ·) ht'
  nlinarith only [hs'', ht'']

 theorem resolventLp_identity (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    s • resolventLp μ hQ s hs - t • resolventLp μ hQ t ht =
      (s-t) • (resolventLp μ hQ t ht).comp (resolventLp μ hQ s hs) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (SobolevSpace.toLp μ hQ)
    (SobolevSpace.resolventAt_identity μ hQ s t hs ht f)
  simpa only [map_sub, map_smul, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, resolventLp_apply] using h

 theorem resolventLp_commute (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Commute (resolventLp μ hQ s hs) (resolventLp μ hQ t ht) := by
  by_cases hst : s = t
  · subst t; exact Commute.refl _
  have h1 := resolventLp_identity μ hQ s t hs ht
  have h2 := resolventLp_identity μ hQ t s ht hs
  have h : (s-t) • ((resolventLp μ hQ s hs).comp (resolventLp μ hQ t ht)) =
      (s-t) • ((resolventLp μ hQ t ht).comp (resolventLp μ hQ s hs)) := by
    linear_combination (norm := module) h1 + h2
  exact smul_right_injective _ (sub_ne_zero.mpr hst) h

 theorem resolventLp_error_energy (t : ℝ) (ht : 0 < t) (v : SobolevSpace μ hQ) :
    ‖resolventLp μ hQ t ht (SobolevSpace.toLp μ hQ v) - SobolevSpace.toLp μ hQ v‖ ^ 2 ≤
      2 * t * SobolevSpace.energy μ hQ v := by
  have h := SobolevSpace.resolventAt_minimizes μ hQ t ht (SobolevSpace.toLp μ hQ v) v
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at h
  have he := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht.le)
    (SobolevSpace.energy_nonneg μ hQ (SobolevSpace.resolventAt μ hQ t ht (SobolevSpace.toLp μ hQ v)))
  change _ ≤ 2 * t * SobolevSpace.energy μ hQ v
  exact le_trans (le_add_of_nonneg_right he) h

end ResolventFamily

section Yosida
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 
noncomputable def yosida (t : ℝ) (ht : 0 < t) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  t⁻¹ • (1 - resolventLp μ hQ t ht)

 theorem yosida_smul (t : ℝ) (ht : 0 < t) :
    t • yosida μ hQ t ht = 1 - resolventLp μ hQ t ht := by
  rw [yosida, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

 theorem yosida_nonneg (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (yosida μ hQ t ht f) := by
  simp only [yosida, smul_apply, sub_apply, one_apply_eq_self, real_inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (resolventLp_sub_identity_inner_nonneg μ hQ t ht f)

 theorem yosida_commute (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Commute (yosida μ hQ s hs) (yosida μ hQ t ht) := by
  have h : Commute (1 - resolventLp μ hQ s hs) (resolventLp μ hQ t ht) :=
    (Commute.one_left _).sub_left (resolventLp_commute μ hQ s t hs ht)
  have hsub := (Commute.one_right _).sub_right h
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro vector
  have hpoint := congrArg (fun operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => operator vector) hsub.eq
  simp only [mul_apply_eq_comp] at hpoint
  simp only [yosida, mul_apply_eq_comp, smul_apply, map_smul]
  rw [smul_comm s⁻¹ t⁻¹, hpoint]

 theorem yosida_resolvent_one (t : ℝ) (ht : 0 < t) :
    yosida μ hQ t ht * resolventLp μ hQ 1 zero_lt_one =
      resolventLp μ hQ t ht * (1 - resolventLp μ hQ 1 zero_lt_one) := by
  have h := resolventLp_identity μ hQ 1 t zero_lt_one ht
  change 1 • resolventLp μ hQ 1 zero_lt_one - t • resolventLp μ hQ t ht =
    (1-t) • (resolventLp μ hQ t ht * resolventLp μ hQ 1 zero_lt_one) at h
  simp only [one_smul] at h
  refine (smul_right_injective (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) ht.ne') ?_
  dsimp only
  rw [← Algebra.smul_mul_assoc, yosida_smul, sub_mul, one_mul, mul_sub, mul_one, smul_sub]
  calc
    resolventLp μ hQ 1 zero_lt_one - resolventLp μ hQ t ht * resolventLp μ hQ 1 zero_lt_one =
      t • resolventLp μ hQ t ht - t • (resolventLp μ hQ t ht * resolventLp μ hQ 1 zero_lt_one) := by
        linear_combination (norm := module) h
    _ = _ := rfl

 theorem yosida_difference_on_core (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (yosida μ hQ s hs - yosida μ hQ t ht) *
        (resolventLp μ hQ 1 zero_lt_one * resolventLp μ hQ 1 zero_lt_one) =
      (resolventLp μ hQ s hs - resolventLp μ hQ t ht) *
        (resolventLp μ hQ 1 zero_lt_one * (1 - resolventLp μ hQ 1 zero_lt_one)) := by
  have hc : Commute (1 - resolventLp μ hQ 1 zero_lt_one) (resolventLp μ hQ 1 zero_lt_one) :=
    (Commute.one_left _).sub_left (Commute.refl _)
  rw [sub_mul, sub_mul, ← mul_assoc, ← mul_assoc, yosida_resolvent_one,
    yosida_resolvent_one, mul_assoc, mul_assoc, hc.eq]

 theorem resolventLp_sub_eq_yosida (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    resolventLp μ hQ s hs - resolventLp μ hQ t ht =
      (t-s) • (resolventLp μ hQ t ht * yosida μ hQ s hs) := by
  have h := resolventLp_identity μ hQ s t hs ht
  change s • resolventLp μ hQ s hs - t • resolventLp μ hQ t ht =
    (s-t) • (resolventLp μ hQ t ht * resolventLp μ hQ s hs) at h
  refine (smul_right_injective (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) hs.ne') ?_
  dsimp only
  rw [smul_comm s (t-s), ← Algebra.mul_smul_comm, yosida_smul]
  simp only [smul_sub, mul_sub, mul_one, sub_smul]
  linear_combination (norm := module) h

 theorem yosida_difference_on_core_eq (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (yosida μ hQ s hs - yosida μ hQ t ht) *
        (resolventLp μ hQ 1 zero_lt_one * resolventLp μ hQ 1 zero_lt_one) =
      (t-s) • ((resolventLp μ hQ t ht * resolventLp μ hQ s hs) *
        ((1 - resolventLp μ hQ 1 zero_lt_one) * (1 - resolventLp μ hQ 1 zero_lt_one))) := by
  rw [yosida_difference_on_core, resolventLp_sub_eq_yosida]
  have hcomp :
      (resolventLp μ hQ t ht * yosida μ hQ s hs) *
          (resolventLp μ hQ 1 zero_lt_one * (1 - resolventLp μ hQ 1 zero_lt_one)) =
        (resolventLp μ hQ t ht * resolventLp μ hQ s hs) *
          ((1 - resolventLp μ hQ 1 zero_lt_one) * (1 - resolventLp μ hQ 1 zero_lt_one)) := by
    rw [mul_assoc (resolventLp μ hQ t ht) (yosida μ hQ s hs),
      ← mul_assoc (yosida μ hQ s hs), yosida_resolvent_one]
    simp only [mul_assoc]
  apply ContinuousLinearMap.ext
  intro vector
  simpa only [mul_apply_eq_comp, smul_apply] using
    congrArg (fun operator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => (t-s) • operator vector) hcomp

 theorem yosida_difference_on_core_norm_le (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℝ 2 μ) :
    ‖(yosida μ hQ s hs - yosida μ hQ t ht)
      (resolventLp μ hQ 1 zero_lt_one (resolventLp μ hQ 1 zero_lt_one f))‖ ≤
      4 * |t-s| * ‖f‖ := by
  have h := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
    (yosida_difference_on_core_eq μ hQ s t hs ht)
  simp only [mul_apply_eq_comp, smul_apply] at h
  rw [h, norm_smul, Real.norm_eq_abs]
  have hD : ∀ g : Lp ℝ 2 μ, ‖(1 - resolventLp μ hQ 1 zero_lt_one) g‖ ≤ 2 * ‖g‖ := by
    intro g
    simp only [sub_apply, one_apply_eq_self]
    have hg := SobolevSpace.resolventAt_norm_le μ hQ 1 zero_lt_one g
    change ‖resolventLp μ hQ 1 zero_lt_one g‖ ≤ ‖g‖ at hg
    exact (norm_sub_le _ _).trans (by linarith)
  have hs' := SobolevSpace.resolventAt_norm_le μ hQ s hs
  have ht' := SobolevSpace.resolventAt_norm_le μ hQ t ht
  change ∀ g, ‖resolventLp μ hQ s hs g‖ ≤ ‖g‖ at hs'
  change ∀ g, ‖resolventLp μ hQ t ht g‖ ≤ ‖g‖ at ht'
  have hb := (ht' _).trans (hs' ((1 - resolventLp μ hQ 1 zero_lt_one) ((1 - resolventLp μ hQ 1 zero_lt_one) f)))
  have hb' := mul_le_mul_of_nonneg_left (hD f) (by norm_num : (0 : ℝ) ≤ 2)
  have hb'' := (hD ((1 - resolventLp μ hQ 1 zero_lt_one) f)).trans hb'
  calc
    _ ≤ |t-s| * (4 * ‖f‖) := mul_le_mul_of_nonneg_left (by linarith [hb.trans hb'']) (abs_nonneg _)
    _ = _ := by ring

variable [ProperSpace X] [BorelSpace X] [μ.Regular]

 theorem resolventLp_eq_zero_iff (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 μ) :
    resolventLp μ hQ t ht f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hr : SobolevSpace.resolventAt μ hQ t ht f = 0 := by
    apply Subtype.ext
    exact h
  have hi (φ : SobolevSpace μ hQ) : inner ℝ f (SobolevSpace.toLp μ hQ φ) = 0 := by
    have h := SobolevSpace.resolventAt_equation μ hQ t ht f φ
    rw [hr] at h
    simpa [energyForm] using h.symm
  have heq : (fun v : Lp ℝ 2 μ => inner ℝ f v) = (fun _ => (0 : ℝ)) :=
    (SobolevSpace.toLp_denseRange μ hQ).equalizer (by fun_prop) (by fun_prop) (funext hi)
  exact inner_self_eq_zero.mp (congrFun heq f)

 theorem resolventLp_injective (t : ℝ) (ht : 0 < t) :
    Function.Injective (resolventLp μ hQ t ht) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (resolventLp_eq_zero_iff μ hQ t ht (f-g)).mp
  rw [map_sub, hfg, sub_self]

 theorem resolventLp_denseRange (t : ℝ) (ht : 0 < t) :
    DenseRange (resolventLp μ hQ t ht) := by
  have h : (resolventLp μ hQ t ht).range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    apply (resolventLp_eq_zero_iff μ hQ t ht f).mp
    apply ext_inner_left ℝ
    intro g
    rw [inner_zero_right, ← resolventLp_inner]
    exact hf _ ⟨g, rfl⟩
  rw [DenseRange, dense_iff_closure_eq]
  simpa only [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe,
    Submodule.top_coe] using congrArg (fun s : Submodule ℝ (Lp ℝ 2 μ) => (s : Set (Lp ℝ 2 μ))) h

 theorem resolventLp_sq_denseRange (t : ℝ) (ht : 0 < t) :
    DenseRange (fun f => resolventLp μ hQ t ht (resolventLp μ hQ t ht f)) :=
  (resolventLp_denseRange μ hQ t ht).comp (resolventLp_denseRange μ hQ t ht)
    (resolventLp μ hQ t ht).continuous

end Yosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

 
noncomputable def expNeg (A : H →L[ℝ] H) (t : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp (t • (-A))

omit [CompleteSpace H] in
 theorem expNeg_zero (A : H →L[ℝ] H) : expNeg A 0 = 1 := by
  simp [expNeg]

 theorem expNeg_add (A : H →L[ℝ] H) (s t : ℝ) :
    expNeg A (s+t) = expNeg A s * expNeg A t := by
  simp only [expNeg, add_smul]
  let : NormedAlgebra ℚ (H →L[ℝ] H) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.exp_add_of_commute (((Commute.refl (-A)).smul_left s).smul_right t)

 theorem expNeg_hasDerivAt (A : H →L[ℝ] H) (t : ℝ) :
    HasDerivAt (expNeg A) ((-A) * expNeg A t) t :=
  hasDerivAt_exp_smul_const' (-A) t

 theorem expNeg_apply_hasDerivAt (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    HasDerivAt (fun s => expNeg A s x) (- A (expNeg A t x)) t := by
  simpa only [mul_apply_eq_comp, neg_apply, map_zero, add_zero] using
    (expNeg_hasDerivAt A t).clm_apply (hasDerivAt_const t x)

 theorem expNeg_norm_apply_le (A : H →L[ℝ] H)
    (hA : ∀ x : H, 0 ≤ inner ℝ x (A x)) (t : ℝ) (ht : 0 ≤ t) (x : H) :
    ‖expNeg A t x‖ ≤ ‖x‖ := by
  have hd (s : ℝ) := (expNeg_apply_hasDerivAt A x s).norm_sq
  have hm : Antitone (fun s : ℝ => ‖expNeg A s x‖ ^ 2) := by
    apply antitone_of_deriv_nonpos (fun s => (hd s).differentiableAt)
    intro s
    rw [(hd s).deriv]
    simpa only [inner_neg_right, RCLike.re_to_real, mul_neg, neg_nonpos] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hA (expNeg A s x))
  have h := hm ht
  simp only [expNeg_zero, one_apply_eq_self] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

 theorem expNeg_norm_le (A : H →L[ℝ] H)
    (hA : ∀ x : H, 0 ≤ inner ℝ x (A x)) (t : ℝ) (ht : 0 ≤ t) :
    ‖expNeg A t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using expNeg_norm_apply_le A hA t ht x

omit [CompleteSpace H] in
 theorem commute_expNeg {A B : H →L[ℝ] H} (h : Commute A B) (s t : ℝ) :
    Commute (expNeg A s) (expNeg B t) := by
  exact (((h.neg_left.neg_right).smul_left s).smul_right t).exp

 theorem expNeg_difference_bound {A B : H →L[ℝ] H}
    (hA : ∀ x : H, 0 ≤ inner ℝ x (A x))
    (hB : ∀ x : H, 0 ≤ inner ℝ x (B x)) (hAB : Commute A B)
    (t : ℝ) (ht : 0 ≤ t) (x : H) :
    ‖expNeg A t x - expNeg B t x‖ ≤ t * ‖(A-B) x‖ := by
  let F : ℝ → H := fun s => expNeg A (t-s) (expNeg B s x)
  have hd (s : ℝ) : HasDerivAt F
      (expNeg A (t-s) (expNeg B s ((A-B) x))) s := by
    have ha := (expNeg_hasDerivAt A (t-s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hb := expNeg_apply_hasDerivAt B x s
    have hBA : Commute (expNeg B s) A :=
      ((hAB.symm.neg_left).smul_left s).exp_left
    have hAA : Commute A (expNeg A (t-s)) :=
      ((Commute.refl A).neg_right.smul_right (t-s)).exp_right
    have hBB : Commute B (expNeg B s) :=
      ((Commute.refl B).neg_right.smul_right s).exp_right
    have hAe (z : H) : A (expNeg A (t-s) z) = expNeg A (t-s) (A z) :=
      congrArg (fun C : H →L[ℝ] H => C z) hAA.eq
    have hBe (z : H) : A (expNeg B s z) = expNeg B s (A z) :=
      congrArg (fun C : H →L[ℝ] H => C z) hBA.symm.eq
    have hBBe (z : H) : B (expNeg B s z) = expNeg B s (B z) :=
      congrArg (fun C : H →L[ℝ] H => C z) hBB.eq
    convert ha.clm_apply hb using 1
    · rfl
    · simp only [sub_apply, map_sub, map_neg, mul_apply_eq_comp,
        neg_apply, zero_sub, one_smul, neg_smul, neg_neg]
      rw [hAe, hBe, hBBe]
      simp only [sub_eq_add_neg, Function.comp_apply]
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖expNeg A (t-s) (expNeg B s ((A-B) x))‖ ≤ ‖(A-B) x‖ := by
    intro s hs
    exact (expNeg_norm_apply_le A hA (t-s) (sub_nonneg.mpr hs.2.le) _).trans
      (expNeg_norm_apply_le B hB s hs.1 _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc (0 : ℝ) t) => (hd s).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  simpa only [F, sub_self, expNeg_zero, one_apply_eq_self,
    sub_zero, norm_sub_rev, mul_comm] using h

end RegularPointCoordinates

end OAI
