import OAI.Probability.InvariantIsing.Haar.HaarVariance
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressure

namespace OAI

/-! Uniform mean absolute fluctuations for constrained Haar pressures. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma integral_abs_sub_mean_le_sqrt_variance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  let g := fun x => f x-∫ y, f y ∂μ
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hga : MemLp (fun x => |g x|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  have hv := variance_nonneg (fun x => |g x|) μ
  rw [variance_eq_sub hga] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have he : (∫ x, g x^2 ∂μ)=variance f μ :=
    (variance_eq_integral hf.aemeasurable).symm
  rw [he] at hv
  apply (sq_le_sq₀ (integral_nonneg (fun _ => abs_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (variance_nonneg f μ)]
  linarith

theorem haar_restrictedPressure_mean_fluctuation (hpub : HaarConcentrationInput) :
    ∃ B : ℝ, 0<B ∧ ∀ N, 3≤N →
      ∀ (μ : Measure (SpecialOrthogonal N)), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
      ∀ (S : Finset (Spin N)), S.Nonempty → ∀ (eig c : Fin N → ℝ) (K : ℝ),
      0<K → (∀ i, |eig i|≤K) →
      Integrable (fun U => restrictedRotatedPressure S eig (specialRotation U) c) μ ∧
      (∫ U, |restrictedRotatedPressure S eig (specialRotation U) c-
        ∫ V, restrictedRotatedPressure S eig (specialRotation V) c ∂μ| ∂μ) ≤
        Real.sqrt (B*K^2/N) := by
  obtain ⟨B,hB,hv⟩ := haar_frobeniusLipschitz_variance hpub
  refine ⟨B,hB,?_⟩
  intro N hN μ hμ hμinv S hS eig c K hK heig
  have : IsProbabilityMeasure μ := hμ
  let f := fun U => restrictedRotatedPressure S eig (specialRotation U) c
  have hm : Measurable f := measurable_restrictedRotatedPressure S eig c
  have hLip : ∀ U V, |f U-f V| ≤ K*frobeniusDistance U V :=
    fun U V => abs_restrictedRotatedPressure_sub_rotation_le (by omega) S hS eig U V c K hK.le heig
  have hf := haar_frobeniusLipschitz_memLp_two hpub N hN μ hμinv f hm K hK hLip
  exact ⟨hf.integrable (by norm_num), (integral_abs_sub_mean_le_sqrt_variance μ f hf).trans
    (Real.sqrt_le_sqrt (hv N hN μ hμ hμinv f hm K hK hLip))⟩

end InvariantIsing

end

end OAI
