import OAI.Geometry.RCD.Sobolev.HamiltonJacobiWeakEnergy
import OAI.Geometry.RCD.Heat.ScaledHeatJointEquation

namespace OAI

/-! # Exact integrated gradient energy for the actual scaled heat flow -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Interval NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_scaled_weak_energy
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε : ℝ} (hε : 0 < ε)
    (z : X) {r : ℝ} (hr : 0 < r) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let H := fun t x => ε * Real.log
      (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν)
    ∃ (w : ℝ → SobolevSpace μ Q) (q : ℝ → Lp ℝ 2 μ),
      (∀ t, 0 < t → IsWeakLaplacian μ Q (w t) (q t) ∧
        SobolevSpace.toLp μ Q (w t) =ᵐ[μ.restrict (closedBall z r)] H t) ∧
      ∀ (φ : SobolevSpace μ Q) (ξ : Lp ℝ 2 μ), IsWeakLaplacian μ Q φ ξ →
        (∀ᵐ x ∂μ, x ∉ closedBall z r → SobolevSpace.toLp μ Q φ x = 0) →
        (∀ᵐ x ∂μ, x ∉ closedBall z r → ξ x = 0) →
        ∀ Bφ : ℝ, (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ Bφ) →
        ∀ c a b : ℝ, 0 < a → a ≤ b → ∀ θ θ' : ℝ → ℝ,
          ContinuousOn θ (Icc a b) → ContinuousOn θ' (Icc a b) →
          (∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t) → θ a = 0 → θ b = 0 →
          (∫ t in a..b, θ t * ∫ x in closedBall z r,
            SobolevSpace.toLp μ Q φ x * localGamma μ Q (w t) (w t) x ∂μ) =
          -2*(∫ t in a..b, θ' t * ∫ x in closedBall z r,
            SobolevSpace.toLp μ Q φ x * (H t x-c) ∂μ) -
          ε*(∫ t in a..b, θ t * ∫ x in closedBall z r, ξ x * (H t x-c) ∂μ) := by
  intro μ Q H
  classical
  obtain ⟨D,hH,hD,hd,hloc⟩ := hX.compact_heat_scaled_joint_equation hn p
    ν ρ hρ hρ0 hB hν F hF hε
  choose v d hv hV hEq using fun t : Ioi (0:ℝ) =>
    hloc t t.property (closedBall z r) (isCompact_closedBall z r)
  let w := fun t => if ht : 0 < t then v ⟨t,ht⟩ else 0
  let q := fun t => if ht : 0 < t then d ⟨t,ht⟩ else 0
  have hdata (t : ℝ) (ht : 0 < t) : IsWeakLaplacian μ Q (w t) (q t) ∧
      (SobolevSpace.toLp μ Q (w t) =ᵐ[μ.restrict (closedBall z r)] H t) ∧
      (D t =ᵐ[μ.restrict (closedBall z r)] fun x => ε/2*q t x + localGamma μ Q (w t) (w t) x/2) := by
    simpa only [w,q,dite_eq_left ht] using ⟨hv ⟨t,ht⟩,hV ⟨t,ht⟩,hEq ⟨t,ht⟩⟩
  refine ⟨w,q,fun t ht => ⟨(hdata t ht).1,(hdata t ht).2.1⟩,?_⟩
  intro φ ξ hξ hφs hξs Bφ hBφ c a b ha hab θ θ' hθ hθ' hder hθa hθb
  exact hamilton_jacobi_weak_energy μ Q H D hH hD hd w q z hr ha hab ε c
    (fun t ht => hdata t (ha.trans_le ht.1)) φ ξ hξ hφs hξs hBφ
    θ θ' hθ hθ' hder hθa hθb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
