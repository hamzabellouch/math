import Mathlib

namespace OAI

noncomputable section
open scoped Topology BoundedContinuousFunction SchwartzMap ContDiff
open Set Filter MeasureTheory
namespace TestSeparation
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integrable_pair (φ : V → ℝ) (hφ : Integrable φ) (f : V →ᵇ E) :
    Integrable (fun x => φ x • f x) := by
  apply (hφ.norm.mul_const ‖f‖).mono'
  · exact hφ.aestronglyMeasurable.smul f.continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

omit [CompleteSpace E] in
lemma norm_pair_le (φ : V → ℝ) (hφ : Integrable φ) (f : V →ᵇ E) :
    ‖∫ x, φ x • f x‖ ≤ (∫ x, ‖φ x‖)*‖f‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono (integrable_pair φ hφ f).norm (hφ.norm.mul_const _)
  intro x
  dsimp only
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

def pairCLM (φ : V → ℝ) (hφ : Integrable φ) : (V →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, φ x • f x
      map_add' := by
        intro f g
        change (∫ x, φ x • (f x+g x)) = _
        simp_rw [smul_add]
        exact integral_add (integrable_pair φ hφ f) (integrable_pair φ hφ g)
      map_smul' := by
        intro c f
        change (∫ x, φ x • (c • f x)) = c • (∫ x, φ x • f x)
        simp_rw [smul_comm (φ _) c]
        exact integral_smul _ _ }
    (∫ x, ‖φ x‖) (fun f => norm_pair_le φ hφ f)

omit [CompleteSpace E] in
@[simp] lemma pairCLM_apply (φ : V → ℝ) (hφ : Integrable φ) (f : V →ᵇ E) :
    pairCLM φ hφ f = ∫ x, φ x • f x := rfl

lemma eq_zero_of_tests (f : V →ᵇ E)
    (h : ∀ (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) f = 0) : f = 0 := by
  have he : ∀ᵐ x, f x=0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    f.continuous.locallyIntegrable (fun φ hφ hc => h φ hφ hc)
  ext x
  exact congrFun (Measure.eq_of_ae_eq he f.continuous continuous_const) x

lemma eq_of_tests (f g : V →ᵇ E)
    (h : ∀ (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) f =
      pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) g) : f=g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_tests
  intro φ hφ hc
  rw [map_sub,h φ hφ hc,sub_self]

lemma integral_eq_sub_of_weak_derivative (u F : ℝ → (V →ᵇ E)) (a b : ℝ) (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hw : ∀ (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∀ t ∈ Ioo a b,
      HasDerivAt (fun r => pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) (u r))
        (pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) (F t)) t) :
    (∫ r in a..b, F r) = u b-u a := by
  apply eq_of_tests
  intro φ hφ hc
  let L := pairCLM (E := E) φ (hφ.continuous.integrable_of_hasCompactSupport hc)
  have hi : IntervalIntegrable F volume a b := hF.intervalIntegrable_of_Icc hab
  rw [map_sub,← L.intervalIntegral_comp_comm hi]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (L.continuous.comp_continuousOn hu) (hw φ hφ hc)
    ((L.continuous.comp_continuousOn hF).intervalIntegrable_of_Icc hab)

lemma hasDerivAt_of_weak_derivative (u F : ℝ → (V →ᵇ E)) (a b t : ℝ)
    (ht : t ∈ Ioo a b) (hu : ContinuousOn u (Icc a b)) (hF : Continuous F)
    (hw : ∀ (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∀ r ∈ Ioo a b,
      HasDerivAt (fun s => pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) (u s))
        (pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc) (F r)) r) :
    HasDerivAt u (F t) t := by
  have he : u =ᶠ[𝓝 t] fun s => u a + ∫ r in a..s, F r := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have h := integral_eq_sub_of_weak_derivative u F a s hs.1.le
      (hu.mono (Icc_subset_Icc_right hs.2.le)) hF.continuousOn
      (fun φ hφ hc r hr => hw φ hφ hc r ⟨hr.1,hr.2.trans hs.2⟩)
    rw [h,add_sub_cancel]
  exact ((intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
    hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).const_add (u a)).congr_of_eventuallyEq he

end TestSeparation

end

end OAI
