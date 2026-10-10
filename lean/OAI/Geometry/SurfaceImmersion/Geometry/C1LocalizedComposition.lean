import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedCompositionBounds

namespace OAI

/-! First-derivative bounds for localization of C1 inputs. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Filter WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localizedComposition_C1 {O : Set Base} (hO : IsOpen O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ O)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O)
    {f : Base → V} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun x => χ x • f (T x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have ht : ContDiffAt ℝ 1 T x :=
      (hT.of_le (by simp)).contDiffAt (hO.mem_nhds (hs hx))
    exact (hχ.of_le (by simp)).contDiffAt.smul (hf.contDiffAt.comp x ht)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    rw [hy,zero_smul]

/-- Localization by a fixed chart change is bounded in C1 even when the
input is only C1. This applies to smoothing errors of a Whitney immersion. -/
theorem compact_localized_C1_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (C : ℝ), 0 ≤ C →
      ContDiff ℝ 1 f → (∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C) →
      ∀ x, ‖χ x • f (T x)‖ ≤ D*C ∧
        ‖fderiv ℝ (fun y => χ y • f (T y)) x‖ ≤ D*C := by
  obtain ⟨A,hA,hAb⟩ := compact_coefficient_bound hO.uniqueDiffOn hK hKO hχ.contDiffOn 1
  obtain ⟨B,hB,hBb⟩ := compact_coefficient_bound hO.uniqueDiffOn hK hKO hT 1
  refine ⟨A+A*B,by positivity,?_⟩
  intro f C hC hf hb x
  by_cases hx : x ∈ tsupport χ
  · have hxO := hKO (hχK hx)
    have hAx : ‖χ x‖ ≤ A := by
      simpa only [norm_iteratedFDerivWithin_zero] using hAb 0 (by omega) x (hχK hx)
    have hA' : ‖fderiv ℝ χ x‖ ≤ A := by
      have hh := hAb 1 le_rfl x (hχK hx)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
        ((hχ.of_le (by simp)).contDiffAt) hxO] at hh
      simpa only [norm_iteratedFDeriv_one] using hh
    have ht := (hT.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffAt (hO.mem_nhds hxO)
    have hB' : ‖fderiv ℝ T x‖ ≤ B := by
      have hh := hBb 1 le_rfl x (hχK hx)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht hxO] at hh
      simpa only [norm_iteratedFDeriv_one] using hh
    refine ⟨?_,?_⟩
    · calc
        ‖χ x • f (T x)‖ = ‖χ x‖*‖f (T x)‖ := norm_smul _ _
        _ ≤ A*C := mul_le_mul hAx (hb _).1 (norm_nonneg _) (by linarith)
        _ ≤ (A+A*B)*C := by nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ B)) hC]
    · have htc := (hf.differentiable one_ne_zero (T x)).comp x
        (ht.differentiableAt one_ne_zero)
      rw [fderiv_fun_smul (f := fun y => f (T y)) (hχ.differentiable (by simp) x) htc]
      change ‖χ x • fderiv ℝ (f ∘ T) x + (fderiv ℝ χ x).smulRight (f (T x))‖ ≤ _
      rw [fderiv_comp x (hf.differentiable one_ne_zero (T x)) (ht.differentiableAt one_ne_zero)]
      calc
        _ ≤ ‖χ x • ((fderiv ℝ f (T x)).comp (fderiv ℝ T x))‖+
            ‖(fderiv ℝ χ x).smulRight (f (T x))‖ := norm_add_le _ _
        _ ≤ ‖χ x‖*(‖fderiv ℝ f (T x)‖*‖fderiv ℝ T x‖)+‖fderiv ℝ χ x‖*‖f (T x)‖ := by
          rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
          exact add_le_add (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)) le_rfl
        _ ≤ A*(C*B)+A*C := by gcongr; exact (hb _).2; exact (hb _).1
        _ = (A+A*B)*C := by ring
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [hz] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy,zero_smul]
    have hval : χ x • f (T x) = 0 := heq.self_of_nhds
    have hd : fderiv ℝ (fun y => χ y • f (T y)) x = 0 := by
      rw [heq.fderiv_eq]
      exact fderiv_const_apply (0 : V)
    rw [hval,hd,norm_zero,norm_zero]
    constructor <;> positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
