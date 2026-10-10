import OAI.Analysis.CircleDomains.Reflection.PrincipalComplexCoefficientData
import OAI.Analysis.CircleDomains.Reflection.CompactReflectionCoefficient
import OAI.Analysis.CircleDomains.Reflection.PrincipalComplexPhysical

namespace OAI

/-! Solve the actual bounded, compact, reflection-invariant coefficient field.
The original coefficient is retained exactly on the circular exterior. -/
open Set Function Filter MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma exists_round_invariant_principal_solution {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0<r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (g : PlaneL2) (F : ℂ ≃ₜ ℂ),
      Measurable E ∧ (∀p,‖E p‖≤k) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      (∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p))) ∧
      (∀ᵐz ∂volume,g z=E (z : Sphere)*(1+beurling g z)) ∧
      Tendsto (fun z => F z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀(v : ℂ) (φ : SchwartzMap ℂ ℂ),HasCompactSupport (φ : ℂ → ℂ) →
        (∫z,F z*fderiv ℝ (φ : ℂ → ℂ) z v)=
          -(∫z,(v+principalDirectionalCorrection g v z)*φ z) := by
  obtain ⟨E,S,hEm,hS,hEb,hEz,hEf,hEinv⟩ := exists_compact_reflection_coefficient c r hr hd μ hm hk hb hz
  have hμm : AEStronglyMeasurable (fun z : ℂ => E (z : Sphere)) volume :=
    (hEm.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable
  obtain ⟨g,F,he,hp,hw⟩ := exists_principal_complex_beltrami_limit (fun z : ℂ => E (z : Sphere))
    hμm hk hk1 (fun z => hEb (z : Sphere)) hEz
  exact ⟨E,g,F,hEm,hEb,hEf,hEinv,he,hp,hw⟩

lemma exists_round_invariant_principal_approximation {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0<r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (T : ℝ) (g : PlaneL2)
      (S : PrincipalSmoothApproximation g k T) (_L : PrincipalMapLimit S),
      Measurable E ∧ (∀z : ℂ,T≤‖z‖ → E (z : Sphere)=0) ∧ (∀p,‖E p‖≤k) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      (∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p))) ∧
      ∀ᵐz ∂volume,g z=E (z : Sphere)*(1+beurling g z) := by
  obtain ⟨E,T,hEm,hT,hEb,hEz,hEf,hEinv⟩ := exists_compact_reflection_coefficient c r hr hd μ hm hk hb hz
  have hμm : AEStronglyMeasurable (fun z : ℂ => E (z : Sphere)) volume :=
    (hEm.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable
  obtain ⟨g,S,L,he⟩ := exists_principal_complex_beltrami_data (fun z : ℂ => E (z : Sphere))
    hμm hk hk1 (fun z => hEb (z : Sphere)) hEz
  exact ⟨E,T,g,S,L,hEm,hEz,hEb,hEf,hEinv,he⟩

lemma exists_round_invariant_principal_approximation_with_coefficient {I : Type*} [Finite I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀i,0<r i)
    (hd : Pairwise (fun i j => Disjoint
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))
      (((↑) : ℂ → Sphere) '' Metric.closedBall (c j) (r j))))
    (μ : ℂ → ℂ) (hm : Measurable μ) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k) (hz : ∀z,R≤‖z‖ → μ z=0) :
    ∃ (E : Sphere → ℂ) (T : ℝ) (g : PlaneL2)
      (S : PrincipalSmoothApproximation g k T) (_L : PrincipalMapLimit S),
      Measurable E ∧ (∀z : ℂ,T≤‖z‖ → E (z : Sphere)=0) ∧ (∀p,‖E p‖≤k) ∧
      EqOn E (sphereCoefficient 0 μ)
        (⋃i,((↑) : ℂ → Sphere) '' Metric.closedBall (c i) (r i))ᶜ ∧
      (∀i p,E p=roundReflectionCoefficient (c i) p
        (E (roundDiskReflection (c i) (r i) (hr i) p))) ∧
      (∀ᵐz ∂volume,g z=E (z : Sphere)*(1+beurling g z)) ∧
      ∀ᵐz ∂volume,Tendsto (fun n => S.coefficient n z) atTop (𝓝 (E (z : Sphere))) := by
  obtain ⟨E,T,hEm,hT,hEb,hEz,hEf,hEinv⟩ := exists_compact_reflection_coefficient c r hr hd μ hm hk hb hz
  have hμm : AEStronglyMeasurable (fun z : ℂ => E (z : Sphere)) volume :=
    (hEm.comp OnePoint.continuous_coe.measurable).aestronglyMeasurable
  obtain ⟨g,S,L,he,hc⟩ := exists_principal_complex_coefficient_data (fun z : ℂ => E (z : Sphere))
    hμm hk hk1 (fun z => hEb (z : Sphere)) hEz
  exact ⟨E,T,g,S,L,hEm,hEz,hEb,hEf,hEinv,he,hc⟩

end CircleDomainRigidity

end

end OAI
