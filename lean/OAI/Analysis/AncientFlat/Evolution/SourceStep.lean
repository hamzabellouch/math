import OAI.Analysis.AncientFlat.Evolution.StrongAction

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def duhamel (T : ℝ → E →L[ℂ] E) (f : ℝ →ᵇ E) (h τ : ℝ) : E :=
  ∫ s in (0:ℝ)..h, T (h-s) (f (τ+s))
variable (T : ℝ → E →L[ℂ] E)
  (hc : ∀ v : E, ContinuousOn (fun t => T t v) (Ici (0:ℝ)))
include hc in
lemma integrand_continuousOn (f : ℝ →ᵇ E) (h τ : ℝ) :
    ContinuousOn (fun s => T (h-s) (f (τ+s))) (Icc (0:ℝ) h) := by
  apply (continuousOn_action T hc).comp
    ((continuous_const.sub continuous_id).prodMk (f.continuous.comp (continuous_const.add continuous_id))).continuousOn
  intro s hs
  exact ⟨show 0≤h-s from sub_nonneg.mpr hs.2,mem_univ _⟩
include hc in
lemma integrand_integrable (f : ℝ →ᵇ E) {h : ℝ} (hh : 0≤h) (τ : ℝ) :
    IntervalIntegrable (fun s => T (h-s) (f (τ+s))) volume 0 h := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hh]
  exact integrand_continuousOn T hc f h τ
include hc in
lemma duhamel_continuous (f : ℝ →ᵇ E) {h : ℝ} (hh : 0≤h) :
    Continuous (duhamel T f h) := by
  have hparam : Continuous (fun p : ℝ × ℝ => T (max 0 (h-p.2)) (f (p.1+p.2))) :=
    (continuous_action_clamp T hc).comp
      ((continuous_const.sub continuous_snd).prodMk (f.continuous.comp (continuous_fst.add continuous_snd)))
  have hi : Continuous (fun τ => ∫ s in Icc (0:ℝ) h, T (max 0 (h-s)) (f (τ+s))) :=
    continuous_parametric_integral_of_continuous hparam isCompact_Icc
  apply hi.congr
  intro τ
  rw [duhamel, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hh]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  dsimp only
  rw [max_eq_right (sub_nonneg.mpr hs.2)]
omit [CompleteSpace E] in
lemma duhamel_norm_le (f : ℝ →ᵇ E) {h : ℝ} (hh : 0≤h) {C : ℝ}
    (hC : ∀ t ∈ Icc (0:ℝ) h, ‖T t‖≤C) (τ : ℝ) :
    ‖duhamel T f h τ‖≤(h*C)*‖f‖ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := h)
    (f := fun s => T (h-s) (f (τ+s))) (C := C*‖f‖) (by
      intro s hs
      rw [uIoc_of_le hh] at hs
      exact ((T (h-s)).le_opNorm_of_le (f.norm_coe_le_norm _)).trans
        (mul_le_mul_of_nonneg_right (hC _ ⟨by linarith [hs.2],by linarith [hs.1]⟩) (norm_nonneg _)))
  simpa only [duhamel,sub_zero,abs_of_nonneg hh,mul_assoc,mul_comm,mul_left_comm] using hb
include hc in
lemma duhamel_add (f g : ℝ →ᵇ E) {h : ℝ} (hh : 0≤h) (τ : ℝ) :
    duhamel T (f+g) h τ=duhamel T f h τ+duhamel T g h τ := by
  simp only [duhamel,BoundedContinuousFunction.add_apply,map_add]
  exact intervalIntegral.integral_add (integrand_integrable T hc f hh τ) (integrand_integrable T hc g hh τ)
omit [CompleteSpace E] in
lemma duhamel_smul (a : ℂ) (f : ℝ →ᵇ E) (h τ : ℝ) :
    duhamel T (a • f) h τ=a • duhamel T f h τ := by
  simp only [duhamel,BoundedContinuousFunction.smul_apply,map_smul,intervalIntegral.integral_smul]
def sourceStep (h : ℝ) (hh : 0≤h) : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E) := by
  let C := Classical.choose (bounded_on T hc h)
  have hC : 0≤C := (Classical.choose_spec (bounded_on T hc h)).1
  have hCb : ∀ t ∈ Icc (0:ℝ) h, ‖T t‖≤C := (Classical.choose_spec (bounded_on T hc h)).2
  let val (f : ℝ →ᵇ E) : ℝ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup
    (duhamel T f h) (duhamel_continuous T hc f hh) ((h*C)*‖f‖) (duhamel_norm_le T f hh hCb)
  let L : (ℝ →ᵇ E) →ₗ[ℂ] (ℝ →ᵇ E) :=
    { toFun := val
      map_add' := fun f g => by ext τ; exact duhamel_add T hc f g hh τ
      map_smul' := fun a f => by ext τ; exact duhamel_smul T a f h τ }
  exact L.mkContinuous (h*C) (fun f => (BoundedContinuousFunction.norm_le (by positivity)).mpr
    (duhamel_norm_le T f hh hCb))
@[simp] lemma sourceStep_apply (h : ℝ) (hh : 0≤h) (f : ℝ →ᵇ E) (τ : ℝ) :
    sourceStep T hc h hh f τ=duhamel T f h τ := by
  unfold sourceStep
  rfl
end AncientMild

end

end OAI
