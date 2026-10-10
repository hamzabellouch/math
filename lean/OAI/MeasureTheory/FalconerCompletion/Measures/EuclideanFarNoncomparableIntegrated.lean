import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SphereAxisIntegralZero

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology

theorem euclidean_far_noncomparable_integratedND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (η : Measure ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
          (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))), ∀ [IsFiniteMeasure η],
      ∀ (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ) (A v : ℝ),
      1≤A → A≤R^2 →
      (∀ᵐ z ∂η,
        R^β≤(2:ℝ)^v*max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        A^2/((2:ℝ)^v*max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2))≤R^(-θ) ∧
        2*min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
        ContDiff ℝ ∞ (b z.1) ∧ ContDiff ℝ ∞ (c z.2) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z.1) w‖≤C*A^j) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c z.2) w‖≤C*A^j)) →
      R^B*‖∫ z, (∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1 z.1.2)*u) (euclideanPairDirectionND z.1) (b z.1)*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist z.2.1 z.2.2)*u) (euclideanPairDirectionND z.2) (c z.2))) ∂η‖≤
            η.real univ*R^(-T) := by
  obtain ⟨J,hJ⟩ := euclidean_far_noncomparable_pointND (n := n) hΨ hs C hC hθ hβ B T
  refine ⟨J,?_⟩
  filter_upwards [hJ,eventually_gt_atTop (0:ℝ)] with R hJ hR
  intro η _ b c A v hA hAup hdata
  have hp := Real.rpow_nonneg hR.le B
  have hh := norm_integral_le_of_norm_le_const (μ := η) (C := R^(-T)) (f := fun z =>
    R^B • (∫ u : ℝ, (Ψ u:ℂ)*
      sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1 z.1.2)*u) (euclideanPairDirectionND z.1) (b z.1)*
        conj (sphereAxisIntegralND (((2:ℝ)^v*dist z.2.1 z.2.2)*u) (euclideanPairDirectionND z.2) (c z.2)))) ?_
  · rw [integral_smul,norm_smul_of_nonneg hp,mul_comm (R^(-T))] at hh
    exact hh
  · filter_upwards [hdata] with z hz
    obtain ⟨hΛ,hrat,hsep,hb,hc,hbd,hcd⟩ := hz
    rw [norm_smul_of_nonneg hp]
    exact hJ (b z.1) (c z.2) z.1 z.2 A v hb hc hA hAup hΛ hrat hsep hbd hcd

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
