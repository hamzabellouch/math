import Mathlib
import OAI.Analysis.Commutator.DecomposableOperator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology ComplexOrder InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma l2_norm_sq (f : Lp H 2 μ) : ‖f‖^2=∫ a,‖f a‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ←integral_re (L2.integrable_inner f f)]
  congr 1
  ext a
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) (f a)).symm

lemma indicator_norm_sq (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s≠⊤) (ξ : H) :
    ‖indicatorConstLp 2 hs hμs ξ‖^2=∫ _ in s,‖ξ‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμs) (c:=ξ)] with a ha
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

lemma operator_indicator_norm_sq (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s≠⊤) (ξ : H) :
    ‖operator μ T hm hb (indicatorConstLp 2 hs hμs ξ)‖^2=∫ a in s,‖T a ξ‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (indicatorConstLp 2 hs hμs ξ),
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμs) (c:=ξ)] with a ha hc
  rw [ha,hc]
  by_cases hx : a∈s <;> simp [hx]

variable [IsFiniteMeasure μ]

lemma fixed_vector_ae_bound (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : 0≤d)
    (hn : ‖operator μ T hm hb‖≤d) (ξ : H) :
    ∀ᵐ a ∂μ,‖T a ξ‖≤d*‖ξ‖ := by
  have hmem : MemLp (fun a => T a ξ) 2 μ := by
    apply (memLp_const ξ).of_le_mul (hm ξ)
    filter_upwards [hb] with a ha
    exact ((T a).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hi := (memLp_two_iff_integrable_sq_norm (hm ξ)).mp hmem
  have hle : (fun a => ‖T a ξ‖^2) ≤ᵐ[μ] (fun _ => (d*‖ξ‖)^2) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _) 
    intro s hs hμs
    let f := indicatorConstLp 2 hs hμs.ne ξ
    have hnorm : ‖operator μ T hm hb f‖≤d*‖f‖ :=
      ((operator μ T hm hb).le_opNorm f).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg f))
    calc
      (∫ a in s,‖T a ξ‖^2 ∂μ)=‖operator μ T hm hb f‖^2 :=
        (operator_indicator_norm_sq μ T hm hb s hs hμs.ne ξ).symm
      _≤(d*‖f‖)^2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg f))).mpr hnorm
      _=d^2*(∫ a in s,‖ξ‖^2 ∂μ) := by rw [mul_pow,indicator_norm_sq μ s hs hμs.ne ξ]
      _=(∫ a in s,(d*‖ξ‖)^2 ∂μ) := by simp only [mul_pow,integral_const_mul]
  filter_upwards [hle] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg ξ))).mp ha

theorem operator_norm_le_iff_ae [TopologicalSpace.SeparableSpace H]
    (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hd : 0≤d) :
    ‖operator μ T hm hb‖≤d ↔ ∀ᵐ a ∂μ,‖T a‖≤d := by
  constructor
  · intro hn
    have htest (n : ℕ) := fixed_vector_ae_bound μ T hm hb hd hn (TopologicalSpace.denseSeq H n)
    filter_upwards [ae_all_iff.mpr htest] with a ha
    apply ContinuousLinearMap.opNorm_le_bound _ hd
    intro ξ
    exact (TopologicalSpace.denseRange_denseSeq H).induction_on ξ
      (isClosed_le (T a).continuous.norm (continuous_const.mul continuous_norm)) (ha)
  · exact operator_norm_le μ T hm hb hd

end Kadison.Decomposable

end

end
end

end OAI
