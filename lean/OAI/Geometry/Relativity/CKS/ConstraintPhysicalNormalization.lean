import OAI.Geometry.Relativity.CKS.IntrinsicReplacementDefinitions

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory CKSLorentz CKSMetricGluing
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M]

lemma physical_normalization [BorelSpace M] [SecondCountableTopology M] (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (h : ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm) :
    IntegrableConstraints g K := by
  obtain ⟨C,Q,hC,hQ,hiC,hiQ,hd,hval⟩ := h
  have hpi : 0 < 8 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨fun x => C x / (8*Real.pi),fun x => Q x / (8*Real.pi),
    hC.div_const _,hQ.div_const _,hiC.div_const _,hiQ.div_const _,?_,?_⟩
  · intro x
    exact ⟨div_nonneg (hd x).1 hpi.le,div_le_div_of_nonneg_right (hd x).2 hpi.le⟩
  · intro x c
    constructor
    · rw [mul_div_cancel₀ _ hpi.ne', (hval x c).1]
    · rw [mul_div_cancel₀ _ hpi.ne', (hval x c).2]

end CKSIntrinsicConstraints

end

end OAI
