import OAI.Geometry.RCD.Metric.ScaledCompactHamiltonJacobi
import OAI.Geometry.RCD.Sobolev.ScaledCompactFactorGradient

namespace OAI

/-! # The exact scaled equation with its uniform local gradient bound

Locality identifies the gradient of the equation's representative with
the independently constructed representative used in the Hamilton bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_scaled_equation_gradient :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0 < F a) →
        ∀ {ε s δ : ℝ} (hε : 0 < ε), ε ≤ 1 → (hδ : 0 < δ) → (hδs : δ ≤ s) → s ≤ 1 →
        ∀ (z : X) (R : ℝ), 0 ≤ R → (∀ a : S, dist z a ≤ R) →
        ∀ (Ω : Set X), IsCompact Ω →
        ∃ (w : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
          IsWeakLaplacian (hausdorff n X) hX.quadratic w q ∧
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[(hausdorff n X).restrict Ω]
            hX.scaledCompactHeatPotential hn p ν F ε s
              (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num))) ∧
          (∀ᵐ x ∂(hausdorff n X).restrict Ω,
            HasDerivAt (fun t => ε * Real.log
              (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν))
              (ε/2*q x + localGamma (hausdorff n X) hX.quadratic w w x/2) s) ∧
          ∀ᵐ x ∂(hausdorff n X).restrict Ω,
            (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic w x)^2 ≤
              Real.exp |K| * (4*C/δ+16*D*(R+dist z x)^2/δ^2) := by
  obtain ⟨C,D,hC,hD,hgrad⟩ := hX.compact_heat_factor_scaled_gradient hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε s δ hε hε1 hδ hδs hs1 z R hR hdist Ω hΩ
  obtain ⟨v,_d,_hd,hv,hvgrad⟩ := hgrad ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1
    z R hR hdist Ω hΩ
  obtain ⟨w,q,hq,hw,hder⟩ := hX.compact_heat_factor_scaled_hamilton_jacobi hn p ν
    ρ hρ hρ0 hB hν F hF hε (hδ.trans_le hδs) hΩ
  refine ⟨w,q,hq,hw,hder,?_⟩
  have heq : SobolevSpace.toLp (hausdorff n X) hX.quadratic w
      =ᵐ[(hausdorff n X).restrict Ω] SobolevSpace.toLp (hausdorff n X) hX.quadratic v :=
    hw.trans hv.symm
  filter_upwards [heq,hvgrad,ae_restrict_of_ae
    (SobolevSpace.minimalSlope_eq_on_eq (hausdorff n X) hX.quadratic w v)] with x hx hb hsl
  rw [hsl hx]
  exact hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
