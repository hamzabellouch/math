import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombKernel

namespace OAI

/-! Finite-box truncation of the bounded Coulomb integral. The bound is
uniform in the displacement and uses only the discarded density masses. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cappedPairIntegrand (ε : ℝ) (shift : Position) (f g : Position → ℝ)
    (p : Position × Position) : ℝ :=
  f p.1 * g p.2 * cappedCoulombKernel ε (p.1 - p.2 - shift)

theorem cappedPairIntegrand_integrable {ε : ℝ} (hε : 0 < ε) (shift : Position)
    {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (cappedPairIntegrand ε shift f g) := by
  have hp : Integrable (fun p : Position × Position => f p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hf.mul_prod hg
  unfold cappedPairIntegrand
  apply hp.mul_bdd (c := ε⁻¹)
    (((cappedCoulombKernel_continuous hε).comp
      ((continuous_fst.sub continuous_snd).sub continuous_const)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖cappedCoulombKernel ε (p.1 - p.2 - shift)‖ ≤ ε⁻¹
    rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
    exact cappedCoulombKernel_le hε _)

theorem cappedPair_truncation_error {ε : ℝ} (hε : 0 < ε) (shift : Position)
    {f g : Position → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    {S T : Set Position} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |(∫ p, cappedPairIntegrand ε shift f g p) -
      ∫ p in S ×ˢ T, cappedPairIntegrand ε shift f g p| ≤
      ε⁻¹ * ((∫ x in Sᶜ, f x) * (∫ y, g y) +
        (∫ x, f x) * (∫ y in Tᶜ, g y)) := by
  let F := cappedPairIntegrand ε shift f g
  let M : Position × Position → ℝ := fun p => ε⁻¹ *
    (Sᶜ.indicator f p.1 * g p.2 + f p.1 * Tᶜ.indicator g p.2)
  have hFi : Integrable F := cappedPairIntegrand_integrable hε shift hf hg
  have hSi := hf.indicator hS.compl
  have hTi := hg.indicator hT.compl
  have hfirst : Integrable (fun p : Position × Position => Sᶜ.indicator f p.1 * g p.2) := by
    simpa only [Measure.volume_eq_prod] using hSi.mul_prod hg
  have hsecond : Integrable (fun p : Position × Position => f p.1 * Tᶜ.indicator g p.2) := by
    simpa only [Measure.volume_eq_prod] using hf.mul_prod hTi
  have hMi : Integrable M := by
    simpa only [M, Pi.add_apply] using (hfirst.add hsecond).const_mul ε⁻¹
  have hpt (p : Position × Position) :
      ‖F p - (S ×ˢ T).indicator F p‖ ≤ M p := by
    have hF0 : 0 ≤ F p := mul_nonneg (mul_nonneg (hf0 _) (hg0 _))
      (cappedCoulombKernel_nonnegative hε _)
    have hFbound : F p ≤ ε⁻¹ * (f p.1 * g p.2) := by
      unfold F cappedPairIntegrand
      calc
        _ ≤ f p.1 * g p.2 * ε⁻¹ := mul_le_mul_of_nonneg_left
          (cappedCoulombKernel_le hε _) (mul_nonneg (hf0 _) (hg0 _))
        _ = _ := by ring
    have hM0 : 0 ≤ M p := mul_nonneg (inv_nonneg.mpr hε.le)
      (add_nonneg
        (mul_nonneg (Set.indicator_nonneg (fun x _ => hf0 x) _) (hg0 _))
        (mul_nonneg (hf0 _) (Set.indicator_nonneg (fun y _ => hg0 y) _)))
    by_cases hs : p.1 ∈ S <;> by_cases ht : p.2 ∈ T
    · rw [Set.indicator_of_mem (show p ∈ S ×ˢ T from ⟨hs, ht⟩), sub_self, norm_zero]
      exact hM0
    · have hp : p ∉ S ×ˢ T := by simp [ht]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      simpa only [M, Set.indicator_of_notMem (show p.1 ∉ Sᶜ by simpa using hs),
        Set.indicator_of_mem (show p.2 ∈ Tᶜ from ht), zero_mul, zero_add] using hFbound
    · have hp : p ∉ S ×ˢ T := by simp [hs]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      simpa only [M, Set.indicator_of_mem (show p.1 ∈ Sᶜ from hs),
        Set.indicator_of_notMem (show p.2 ∉ Tᶜ by simpa using ht), mul_zero, add_zero] using hFbound
    · have hp : p ∉ S ×ˢ T := by simp [hs]
      rw [Set.indicator_of_notMem hp, sub_zero, Real.norm_of_nonneg hF0]
      dsimp only [M]
      rw [Set.indicator_of_mem (show p.1 ∈ Sᶜ from hs),
        Set.indicator_of_mem (show p.2 ∈ Tᶜ from ht)]
      have hz := mul_nonneg (inv_nonneg.mpr hε.le) (mul_nonneg (hf0 p.1) (hg0 p.2))
      linarith
  rw [← integral_indicator (hS.prod hT), ← integral_sub hFi (hFi.indicator (hS.prod hT))]
  have h := norm_integral_le_of_norm_le
    (f := fun p => F p - (S ×ˢ T).indicator F p) hMi (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  simp only [M, integral_const_mul]
  rw [integral_add hfirst hsecond, Measure.volume_eq_prod, integral_prod_mul, integral_prod_mul,
    integral_indicator hS.compl, integral_indicator hT.compl]

end ContinuumCoulomb

end

end OAI
