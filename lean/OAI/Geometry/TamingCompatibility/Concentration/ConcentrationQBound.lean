import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationTest
import OAI.Geometry.TamingCompatibility.DifferentialForms.PhysicalSchur

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [SecondCountableTopology X] in
lemma concentrationTest_Q_bound (Q : L2 A J α hs ht true) (p : A.centers) :
    ∃ B C L : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 < L ∧
      ∀ r : ℝ, ∀ hr : 0 < r, ∀ x : X, ∀ hx : x ∈ tsupport (A.partition p),
      ∀ v : Space,
      |⟪Q,smoothL2 A J α hs ht true (concentrationTest A J α ht E hE p r hr x hx v)⟫| ≤
      (B*physicalQError A J α hs ht (l2Coefficients A J α hs ht E hE Q) L r x+C*r^4)*‖v‖ := by
  let := geometricVolume_finite A J α hs ht
  let q := l2Coefficients A J α hs ht E hE Q
  have hq : Integrable q (geometricVolume A J α) := (Lp.memLp q).integrable (by norm_num)
  obtain ⟨B,C,L,hB,hC,hL,hbound⟩ := concentrationTest_coefficient_physical A J α hs ht E hE p
  refine ⟨B,C*(∫ y, ‖q y‖ ∂geometricVolume A J α),L,hB,
    mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _)),hL,fun r hr x hx v => ?_⟩
  let a := concentrationTest A J α ht E hE p r hr x hx v
  rw [l2Coefficients_pairing A J α hs ht E hE Q a]
  have hi := physicalQError_integrand_integrable A J α hs ht q hq hL hr x
  have hq' : Integrable (fun y => (C*r^4)*‖q y‖) (geometricVolume A J α) := hq.norm.const_mul _
  have hi' : Integrable (fun y => B*(‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3))
      (geometricVolume A J α) := hi.const_mul B
  have htot := (hi'.add hq').mul_const ‖v‖
  have hp (y : X) : ‖⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫‖ ≤
      (B*(‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3)+(C*r^4)*‖q y‖)*‖v‖ :=
    (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (hbound r hr x hx v y)
      (norm_nonneg (q y))).trans_eq (by ring))
  have hh := norm_integral_le_of_norm_le htot (ae_of_all _ hp)
  change |∫ y, ⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫ ∂geometricVolume A J α| ≤ _
  rw [integral_mul_const] at hh
  simp only [Pi.add_apply] at hh
  rw [integral_add hi' hq',integral_const_mul,integral_const_mul] at hh
  rw [Real.norm_eq_abs] at hh
  change |∫ y, ⟪q y,normalizedFrameEncode A J α ht E y (a.val y)⟫ ∂geometricVolume A J α| ≤
    (B*(∫ y, ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3 ∂geometricVolume A J α)+
      (C*(∫ y, ‖q y‖ ∂geometricVolume A J α))*r^4)*‖v‖
  exact hh.trans_eq (by ring)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
