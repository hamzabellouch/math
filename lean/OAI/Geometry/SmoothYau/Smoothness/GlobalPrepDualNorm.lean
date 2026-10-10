import Mathlib
import OAI.Geometry.SmoothYau.Geometry.PulledGradientNorm

namespace OAI

noncomputable section
section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Function
open scoped Topology ContDiff
variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_translate {f : V → F} (hf : ContDiff ℝ ∞ f) (τ : V) :
    ContDiff ℝ ∞ (fun v => f (v+τ)) := hf.comp (contDiff_id.add contDiff_const)

lemma fderiv_translate {f : V → F} (hf : ContDiff ℝ ∞ f) (τ z : V) :
    fderiv ℝ (fun v => f (v+τ)) z = fderiv ℝ f (z+τ) := by
  have hh : HasFDerivAt (fun v : V => v+τ) (ContinuousLinearMap.id ℝ V) z := by
    simpa using (hasFDerivAt_id z).add_const τ
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using ((hf.differentiable (by simp) (z+τ)).hasFDerivAt.comp z hh).fderiv

theorem preparation_remainder_uniform_phase
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B₀ B₁ : ℝ)
    (hB₀ : ∀ z, |F₀ z| ≤ B₀) (hB₁ : ∀ z, ‖fderiv ℝ F₀ z‖ ≤ B₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ), 1 ≤ N → ∀ τ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ (fun z => F₀ (z+τ)) y (d/N) N x‖ ≤ C/N := by
  obtain ⟨Y₂,hY₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ y)
    (continuous_coordinateCovariantSecond Γ hΓ hy).continuousOn
  obtain ⟨Y₁,hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y) (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₂,hD₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ χ)
    (continuous_coordinateCovariantSecond Γ hΓ hχ).continuousOn
  obtain ⟨D₁,hD₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ χ) (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₀,hD₀⟩ := hK.exists_bound_of_continuousOn (f := χ) hχ.continuous.continuousOn
  let A := |d| *|D₀| *|B₁| *|Y₂| +2*|d| *|D₁| *|B₁| *|Y₁| +|d| *|B₀| *|D₂|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,?_⟩
  intro N hN τ x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY₂x := (hY₂ x hx).trans (le_abs_self Y₂)
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hD₂x := (hD₂ x hx).trans (le_abs_self D₂)
  have hD₁x := (hD₁ x hx).trans (le_abs_self D₁)
  have hD₀x : |χ x| ≤ |D₀| := (hD₀ x hx).trans (le_abs_self D₀)
  have hF₀x := (hB₀ (N • y x+τ)).trans (le_abs_self B₀)
  have hF₁x : ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖ ≤ |B₁| := by
    rw [fderiv_translate hF]
    exact (hB₁ _).trans (le_abs_self B₁)
  have he : |d/N/N| ≤ |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    exact div_le_self (div_nonneg (abs_nonneg _) hNp.le) hN
  calc
    _ ≤ |d/N| *|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖coordinateCovariantSecond Γ y x‖ +
        2*|d/N| *‖fderiv ℝ χ x‖*‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖ +
        |d/N/N| *|F₀ (N • y x+τ)| *‖coordinateCovariantSecond Γ χ x‖ :=
      corrugationSecondRemainder_norm_bound Γ hψ hχ (smooth_translate hF τ) hy (d/N) N hNp.ne' x
    _ ≤ (|d|/N)*|D₀| *|B₁| *|Y₂| +2*(|d|/N)*|D₁| *|B₁| *|Y₁| +(|d|/N)*|B₀| *|D₂| := by
      rw [abs_div,abs_of_pos hNp]
      gcongr
    _ = A/N := by dsimp [A]; ring
    _ ≤ (A+1)/N := div_le_div_of_nonneg_right (by linarith) hNp.le

def preparationCorrugation (ψ χ : E → ℝ) (F₀ : V → ℝ) (y : E → V)
    (d N : ℝ) (τ : V) (x : E) : ℝ :=
  ψ x+(d/N/N)*(χ x*F₀ (N • y x+τ))

lemma preparationCorrugation_smooth {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (τ : V) :
    ContDiff ℝ ∞ (preparationCorrugation ψ χ F₀ y d N τ) :=
  hψ.add (contDiff_const.mul (hχ.mul (hF.comp ((hy.const_smul N).add contDiff_const))))

theorem preparation_C1_uniform_phase
    {ψ χ : E → ℝ} {F₀ : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F₀) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B₀ B₁ : ℝ)
    (hB₀ : ∀ z, |F₀ z| ≤ B₀) (hB₁ : ∀ z, ‖fderiv ℝ F₀ z‖ ≤ B₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ), 1 ≤ N → ∀ τ : V, ∀ x ∈ K,
      |preparationCorrugation ψ χ F₀ y d N τ x-ψ x| ≤ C/N ∧
      ‖fderiv ℝ (preparationCorrugation ψ χ F₀ y d N τ) x-fderiv ℝ ψ x‖ ≤ C/N := by
  obtain ⟨Y₁,hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y)
    (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₁,hD₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ χ)
    (hχ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨D₀,hD₀⟩ := hK.exists_bound_of_continuousOn (f := χ) hχ.continuous.continuousOn
  let A := |d| * |D₀| * |B₀| + |d| * |D₁| * |B₀| + |d| * |D₀| * |B₁| * |Y₁|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,?_⟩
  intro N hN τ x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hD₁x := (hD₁ x hx).trans (le_abs_self D₁)
  have hD₀x : |χ x| ≤ |D₀| := (hD₀ x hx).trans (le_abs_self D₀)
  have hF₀x := (hB₀ (N • y x+τ)).trans (le_abs_self B₀)
  have hF₁x : ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖ ≤ |B₁| := by
    rw [fderiv_translate hF]
    exact (hB₁ _).trans (le_abs_self B₁)
  have he : |d/N/N| ≤ |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    exact div_le_self (div_nonneg (abs_nonneg _) hNp.le) hN
  have heN : |d/N/N| *N = |d|/N := by
    rw [abs_div,abs_div,abs_of_pos hNp]
    field_simp
  have hC : (|d| *|D₀| *|B₀|)/N ≤ (A+1)/N := by
    apply div_le_div_of_nonneg_right _ hNp.le
    dsimp [A]
    nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₁)) (abs_nonneg B₀),
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₀)) (abs_nonneg B₁)) (abs_nonneg Y₁)]
  constructor
  · calc
      _ = |d/N/N| * |χ x| * |F₀ (N • y x+τ)| := by
        simp only [preparationCorrugation,add_sub_cancel_left,abs_mul]; ring
      _ ≤ (|d|/N)*|D₀| *|B₀| := by gcongr
      _ = (|d| *|D₀| *|B₀|)/N := by ring
      _ ≤ (A+1)/N := hC
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hdv : (fderiv ℝ (preparationCorrugation ψ χ F₀ y d N τ) x-fderiv ℝ ψ x) v =
        (d/N/N)*fderiv ℝ χ x v*F₀ (N • y x+τ)+
        (d/N/N)*χ x*N*fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v) := by
      have hh := corrugation_first hψ hχ (smooth_translate hF τ) hy (d/N/N) N x v
      have heq : preparationCorrugation ψ χ F₀ y d N τ =
          fun z => ψ z+(d/N/N)*χ z*F₀ (N • y z+τ) := by
        funext z; dsimp [preparationCorrugation]; ring
      rw [heq,sub_apply,hh]
      ring
    rw [hdv]
    calc
      _ ≤ |d/N/N| *‖fderiv ℝ χ x‖*‖v‖*|F₀ (N • y x+τ)|+
          |d/N/N| *|χ x| *N*‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖ := by
        have hbχ : |fderiv ℝ χ x v| ≤ ‖fderiv ℝ χ x‖*‖v‖ := (fderiv ℝ χ x).le_opNorm v
        have hbF : |fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v)| ≤
            ‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*(‖fderiv ℝ y x‖*‖v‖) :=
          ((fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((fderiv ℝ y x).le_opNorm v) (norm_nonneg _))
        calc
          _ ≤ |d/N/N| * |fderiv ℝ χ x v| * |F₀ (N • y x+τ)|+
              |d/N/N| * |χ x| * N * |fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v)| := by
            simpa only [norm_mul,Real.norm_eq_abs,abs_of_pos hNp] using norm_add_le
              ((d/N/N)*fderiv ℝ χ x v*F₀ (N • y x+τ))
              ((d/N/N)*χ x*N*fderiv ℝ (fun z => F₀ (z+τ)) (N • y x) (fderiv ℝ y x v))
          _ ≤ |d/N/N| * (‖fderiv ℝ χ x‖*‖v‖) * |F₀ (N • y x+τ)|+
              |d/N/N| * |χ x| * N * (‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*(‖fderiv ℝ y x‖*‖v‖)) := by gcongr
          _ = _ := by ring
      _ = |d/N/N| *‖fderiv ℝ χ x‖*‖v‖*|F₀ (N • y x+τ)|+
          (|d|/N)*|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖ := by
        have hh := congrArg (fun t => t*|χ x| *‖fderiv ℝ (fun z => F₀ (z+τ)) (N • y x)‖*‖fderiv ℝ y x‖*‖v‖) heN
        nlinarith only [hh]
      _ ≤ (|d|/N)*|D₁| *‖v‖*|B₀|+(|d|/N)*|D₀| *|B₁| *|Y₁| *‖v‖ := by gcongr
      _ = ((|d| *|D₁| *|B₀|+|d| *|D₀| *|B₁| *|Y₁|)/N)*‖v‖ := by ring
      _ ≤ ((A+1)/N)*‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        apply div_le_div_of_nonneg_right _ hNp.le
        dsimp [A]
        nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg d) (abs_nonneg D₀)) (abs_nonneg B₀)]

end YauCounterexamples

end

open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

def preparationWave (t : ℝ) : ℝ := -Real.cos (2*Real.pi*t)/(2*Real.pi^2)

def preparationWaveFirst (t : ℝ) : ℝ := Real.sin (2*Real.pi*t)/Real.pi

def preparationWaveSecond (t : ℝ) : ℝ := 2*Real.cos (2*Real.pi*t)

lemma preparationWave_smooth : ContDiff ℝ ∞ preparationWave :=
  ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).neg).div_const _

lemma preparationWave_hasDeriv (t : ℝ) : HasDerivAt preparationWave (preparationWaveFirst t) t := by
  have hb : HasDerivAt (fun z : ℝ => 2*Real.pi*z) (2*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2*Real.pi)
  have hh := hb.cos.neg.div_const (2*Real.pi^2)
  have he : -(-Real.sin (2*Real.pi*t)*(2*Real.pi))/(2*Real.pi^2) = preparationWaveFirst t := by
    dsimp [preparationWaveFirst]
    field_simp [Real.pi_ne_zero]
  rw [he] at hh
  exact hh

lemma preparationWaveFirst_hasDeriv (t : ℝ) :
    HasDerivAt preparationWaveFirst (preparationWaveSecond t) t := by
  have hb : HasDerivAt (fun z : ℝ => 2*Real.pi*z) (2*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2*Real.pi)
  have hh := hb.sin.div_const Real.pi
  have he : Real.cos (2*Real.pi*t)*(2*Real.pi)/Real.pi = preparationWaveSecond t := by
    dsimp [preparationWaveSecond]
    field_simp [Real.pi_ne_zero]
  rw [he] at hh
  exact hh

lemma preparationWave_deriv : deriv preparationWave = preparationWaveFirst := by
  funext t
  exact (preparationWave_hasDeriv t).deriv

lemma preparationWave_second : deriv (deriv preparationWave) = preparationWaveSecond := by
  rw [preparationWave_deriv]
  funext t
  exact (preparationWaveFirst_hasDeriv t).deriv

lemma preparationWave_abs_bound (t : ℝ) : |preparationWave t| ≤ 1/(2*Real.pi^2) := by
  dsimp [preparationWave]
  rw [abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi^2)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

lemma preparationWave_deriv_bound (t : ℝ) : ‖fderiv ℝ preparationWave t‖ ≤ 1/Real.pi := by
  rw [←norm_deriv_eq_norm_fderiv,preparationWave_deriv]
  dsimp [preparationWaveFirst]
  rw [abs_div,abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) Real.pi_pos.le

lemma preparationWave_second_bound (t : ℝ) : |preparationWaveSecond t| ≤ 2 := by
  dsimp [preparationWaveSecond]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [Real.abs_cos_le_one (2*Real.pi*t)]

lemma preparationWaveSecond_smooth : ContDiff ℝ ∞ preparationWaveSecond :=
  contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

lemma preparationWave_periodic : Function.Periodic preparationWave 1 := by
  intro t
  dsimp [preparationWave]
  rw [show 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi by ring,Real.cos_add_two_pi]

lemma preparationWaveSecond_periodic : Function.Periodic preparationWaveSecond 1 := by
  intro t
  dsimp [preparationWaveSecond]
  rw [show 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi by ring,Real.cos_add_two_pi]

lemma scalar_second_fderiv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t v w : ℝ) :
    fderiv ℝ (fderiv ℝ f) t v w = deriv (deriv f) t * v * w := by
  have hh : (fun z => fderiv ℝ f z w) = fun z => deriv f z*w := by
    funext z
    exact fderiv_eq_deriv_mul
  have he : fderiv ℝ (fun z => fderiv ℝ f z w) t =
      (fderiv ℝ (fderiv ℝ f) t).flip w := by
    rw [fderiv_clm_apply
      ((hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp) t)
      (differentiableAt_const w)]
    simp
  rw [←ContinuousLinearMap.flip_apply,←he,hh]
  have hd : ContDiff ℝ ∞ (deriv f) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_mul_const (hd.differentiable (by simp) t)]
  simp only [smul_apply,smul_eq_mul,fderiv_eq_deriv_mul]
  ring

end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance globalPrepDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance globalPrepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance globalPrepFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance globalPrepFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance globalPrepInvNorm : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance globalPrepInvSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance

def actualCoordinateNorm (g : SmoothMetric E E) (x : E) (v : E) : ℝ :=
  Real.sqrt (selfMetricFlat g x v v)

def actualProfileSpeed (g : SmoothMetric E E) (u : E → ℝ) (x : E) : ℝ :=
  actualCoordinateNorm g x (coordinateMetricGradient g u x)

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_eq (g : SmoothMetric E E) (x v : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    actualCoordinateNorm g x v = ‖(NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  have he := selfMetricFlat_metric_norm g x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm v)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at he
  rw [actualCoordinateNorm,he,Real.sqrt_sq (norm_nonneg _)]

lemma actualProfileSpeed_eq (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    actualProfileSpeed g u x = ‖metricGradient g u x‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [actualProfileSpeed,actualCoordinateNorm_eq,coordinateMetricGradient_eq,
    ContinuousLinearEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_nonneg (g : SmoothMetric E E) (x v : E) :
    0 ≤ actualCoordinateNorm g x v := Real.sqrt_nonneg _

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_pos (g : SmoothMetric E E) (x : E) {v : E} (hv : v ≠ 0) :
    0 < actualCoordinateNorm g x v := Real.sqrt_pos.mpr (selfMetricFlat_pos g x hv)

omit [FiniteDimensional ℝ E] in
lemma continuous_actualCoordinateNorm (g : SmoothMetric E E) {v : E → E}
    (hv : Continuous v) : Continuous (fun x => actualCoordinateNorm g x (v x)) :=
  (((contDiff_selfMetricFlat g).continuous.clm_apply hv).clm_apply hv).sqrt

lemma continuous_actualProfileSpeed (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (actualProfileSpeed g u) :=
  continuous_actualCoordinateNorm g (contDiff_coordinateMetricGradient g hu).continuous

omit [FiniteDimensional ℝ E] in
lemma actualCoordinateNorm_abs_sub (g : SmoothMetric E E) (x v w : E) :
    |actualCoordinateNorm g x v-actualCoordinateNorm g x w| ≤ actualCoordinateNorm g x (v-w) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  simp only [actualCoordinateNorm_eq,map_sub]
  exact abs_norm_sub_norm_le _ _

theorem compact_actual_gradient_error (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ u v : E → ℝ, ∀ x ∈ K,
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
        D*‖fderiv ℝ v x-fderiv ℝ u x‖ := by
  have hi : Continuous (fun x => (selfMetricFlat g x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt).continuousAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f:=selfMetricFlat g) (contDiff_selfMetricFlat g).continuous.continuousOn
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (f:=fun x => (selfMetricFlat g x).inverse) hi.continuousOn
  let C := |B|+|A|+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg B,abs_nonneg A]
  have hCB : ∀ x ∈ K, ‖selfMetricFlat g x‖ ≤ C := by
    intro x hx
    exact (hB x hx).trans (by dsimp [C]; linarith [le_abs_self B,abs_nonneg A])
  have hCA : ∀ x ∈ K, ‖(selfMetricFlat g x).inverse‖ ≤ C := by
    intro x hx
    exact (hA x hx).trans (by dsimp [C]; linarith [le_abs_self A,abs_nonneg B])
  have hnorm : ∀ x ∈ K, ∀ w : E, actualCoordinateNorm g x w ≤ C*‖w‖ := by
    intro x hx w
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hC.le (norm_nonneg _),?_⟩
    have hBww := (le_abs_self (selfMetricFlat g x w w)).trans
      ((selfMetricFlat g x).le_opNorm₂ w w)
    have hh := mul_le_mul_of_nonneg_right (hCB x hx) (sq_nonneg ‖w‖)
    have hc2 : C ≤ C ^ 2 := by nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖w‖)
    nlinarith
  refine ⟨C ^ 2,sq_pos_of_pos hC,?_⟩
  intro u v x hx
  have hg : coordinateMetricGradient g v x-coordinateMetricGradient g u x =
      (selfMetricFlat g x).inverse (fderiv ℝ v x-fderiv ℝ u x) := (map_sub _ _ _).symm
  rw [hg]
  calc
    _ ≤ C*‖(selfMetricFlat g x).inverse (fderiv ℝ v x-fderiv ℝ u x)‖ := hnorm x hx _
    _ ≤ C*(‖(selfMetricFlat g x).inverse‖*‖fderiv ℝ v x-fderiv ℝ u x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hC.le
    _ ≤ C*(C*‖fderiv ℝ v x-fderiv ℝ u x‖) := by gcongr; exact hCA x hx
    _ = _ := by ring

lemma compact_actual_speed_pos (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (ha : ∀ x ∈ K, coordinateMetricGradient g u x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ actualProfileSpeed g u x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne (continuous_actualProfileSpeed g hu).continuousOn
    exact ⟨_,actualCoordinateNorm_pos g x (ha x hx),hm⟩
  · exact ⟨1,zero_lt_one,fun x hx => (hne ⟨x,hx⟩).elim⟩

lemma actualJet_eventuallyEq (g : SmoothMetric E E) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) :
    coordinateMetricGradient g u x = coordinateMetricGradient g v x ∧
    actualCoordinateHessian g u x = actualCoordinateHessian g v x ∧
    (actualProfileStrict g u x ↔ actualProfileStrict g v x) ∧
    (actualProfileFull g u x ↔ actualProfileFull g v x) := by
  have h₁ := h.fderiv_eq (𝕜:=ℝ)
  have h₂ := (h.fderiv (𝕜:=ℝ)).fderiv_eq (𝕜:=ℝ)
  have hg : coordinateMetricGradient g u x = coordinateMetricGradient g v x := by
    simp only [coordinateMetricGradient,h₁]
  have hh : actualCoordinateHessian g u x = actualCoordinateHessian g v x := by
    simp only [actualCoordinateHessian,coordinateCovariantSecond,h₁,h₂]
  exact ⟨hg,hh,by simp only [actualProfileStrict,actualProfileTraceForm,hg,hh,h₁],
    by simp only [actualProfileFull,actualProfileTraceForm,hg,hh,h₁]⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma preparationCorrugation_eventuallyEq (u χ s : E → ℝ) (C N τ : ℝ) {x : E}
    (hx : x ∉ tsupport χ) :
    preparationCorrugation u χ preparationWave s C N τ =ᶠ[𝓝 x] u := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [preparationCorrugation,hy,Pi.zero_apply,zero_mul,mul_zero,add_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma preparationCorrugation_tsupport (u χ s : E → ℝ) (C N τ : ℝ) :
    tsupport (fun x => preparationCorrugation u χ preparationWave s C N τ x-u x) ⊆
      tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx
  simp [Function.mem_support,preparationCorrugation,hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma disjoint_sum_eventuallyEq {ι : Type*} [Fintype ι]
    (u : E → ℝ) (f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (f i))) (x : E) :
    ((fun y => u y+∑ i, f i y) =ᶠ[𝓝 x] u) ∨
      ∃ i, x ∈ tsupport (f i) ∧
        (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  by_cases hx : ∃ i, x ∈ tsupport (f i)
  · obtain ⟨i,hi⟩ := hx
    right
    refine ⟨i,hi,?_⟩
    have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
      · exact (notMem_tsupport_iff_eventuallyEq.mp ((hd hji).notMem_of_mem_right hi)).mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]
  · left
    have hz : ∀ i, ∀ᶠ y in 𝓝 x, f i y = 0 := fun i =>
      notMem_tsupport_iff_eventuallyEq.mp (fun hh => hx ⟨i,hh⟩)
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    simp only [hy,Finset.sum_const_zero,add_zero]

theorem compact_relative_gradient_tolerance (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (ha : ∀ x ∈ K, coordinateMetricGradient g u x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : E → ℝ, ∀ x ∈ K,
      ‖fderiv ℝ v x-fderiv ℝ u x‖ < δ →
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) <
        ε*actualProfileSpeed g u x := by
  obtain ⟨D,hD,hbound⟩ := compact_actual_gradient_error g hK
  obtain ⟨m,hm,hmin⟩ := compact_actual_speed_pos g hu hK ha
  refine ⟨ε*m/D,by positivity,?_⟩
  intro v x hx hd
  calc
    _ ≤ D*‖fderiv ℝ v x-fderiv ℝ u x‖ := hbound u v x hx
    _ < D*(ε*m/D) := mul_lt_mul_of_pos_left hd hD
    _ = ε*m := by field_simp
    _ ≤ ε*actualProfileSpeed g u x := mul_le_mul_of_nonneg_left (hmin x hx) hε.le

end
end YauCounterexamples

end OAI
