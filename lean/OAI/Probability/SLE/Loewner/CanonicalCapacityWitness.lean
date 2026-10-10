import OAI.Probability.SLE.Loewner.CanonicalHydrodynamic
import OAI.Probability.SLE.Loewner.CanonicalFlowEvolution

namespace OAI

/-! All components of the raw capacity-two witness on the normalized
Wiener space, using the same continuous trace modification throughout. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem exists_canonical_capacity_witness
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∃ Ψ : Target.Driver → C(ℝ≥0,ℂ), Measurable Ψ ∧
      ∀ᵐ b ∂W, IsCapacityTwoWitness (fun t => b (κ.toNNReal*t)) (Ψ b)
        (fun t z => Target.flow κ b z (κ*t))
        (fun t z => Target.inverseFlow κ b (κ*t) z) := by
  obtain ⟨Ψ,hΨ,hΨeq,htrace⟩ := exists_canonical_all_time_boundary_limit
    κ hκ hκ8 B hB hm hc h0 γ G F hw W hW
  have hsurv := ae_canonical_survival κ hκ B hB hm hc h0 γ G F hw W hW Ψ hΨ hΨeq
  have hhol := ae_canonical_inverse_holomorphic κ hκ B hB hm hc h0 γ G F hw W hW
  have hnonzero := ae_canonical_inverse_deriv_ne_zero κ hκ B hB hm hc h0 γ G F hw W hW
  have hinfty := ae_canonical_dense_infinity κ hκ B hB hm hc h0 γ G F hw W hW
  refine ⟨Ψ,hΨ,?_⟩
  filter_upwards [htrace,hsurv,hhol,hnonzero,hinfty] with b htr hD hF hF' hnorm
  have hset (T : ℝ≥0) : {z | Target.Surviving κ b z (κ*T)}=survivingDomain (Ψ b) T := by
    ext z
    exact hD T z
  have hG (T : ℝ≥0) : DifferentiableOn ℂ (fun z => Target.flow κ b z (κ*T))
      (survivingDomain (Ψ b) T) := by
    have hf : DifferentiableOn ℂ (Target.inverseFlow κ b (κ.toNNReal*T)) upperHalfPlane := by
      simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using hF T
    have hf' : ∀ w ∈ upperHalfPlane,
        deriv (Target.inverseFlow κ b (κ.toNNReal*T)) w ≠ 0 := by
      simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using hF' T
    simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le,hset] using
      Target.differentiableOn_flow_of_inverse κ hκ b (κ.toNNReal*T) hf hf'
  refine ⟨(Ψ b).continuous,htr.1,htr.2.1,hG,hF,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro T z hz
    exact Target.surviving_flow_mem_upperHalfPlane κ b z (κ*T)
      (mul_nonneg hκ.le T.coe_nonneg) ((hD T z).mpr hz)
  · intro T z hz
    apply (hD T _).mp
    simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using
      Target.inverseFlow_surviving κ hκ b (κ.toNNReal*T) z hz
  · intro T z hz
    exact Target.inverseFlow_eq_of_surviving κ b (κ*T)
      (mul_nonneg hκ.le T.coe_nonneg) z _ ((hD T z).mpr hz) rfl
  · intro T z hz
    simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using
      Target.flow_inverseFlow κ hκ b (κ.toNNReal*T) z hz
  · intro z hz
    simpa only [NNReal.coe_zero,mul_zero] using Target.flow_zero κ b z hz
  · intro T z hz
    exact canonical_flow_time_derivative κ hκ b (Ψ b) hD T z hz
  · intro T
    have hcont : ContinuousOn (fun z => z*(Target.flow κ b z (κ*T)-z))
        (survivingDomain (Ψ b) T) :=
      continuous_id.continuousOn.mul ((hG T).continuousOn.sub continuous_id.continuousOn)
    have hn : DenseInfinityCriterion (fun z => z*(Target.flow κ b z (κ*T)-z))
        (survivingDomain (Ψ b) T) (2*(T:ℂ)) := by
      simpa only [hset] using hnorm T
    exact hn.tendsto (isOpen_survivingDomain (Ψ b).continuous T) hcont
  · intro T
    simpa only [Target.rawTipAt,NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using htr.2.2 T

end SLEExactGauge

end

end OAI
