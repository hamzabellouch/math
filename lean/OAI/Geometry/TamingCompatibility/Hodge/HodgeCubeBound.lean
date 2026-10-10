import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCommutatorCover

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
lemma norm_cube_combination_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (B₁ B₂ B₃ N : ℝ) (u₁ u₂ u₃ : E)
    (h₁ : ‖u₁‖ ≤ B₁*r⁻¹*N) (h₂ : ‖u₂‖ ≤ B₂*(r⁻¹)^3*N)
    (h₃ : ‖u₃‖ ≤ B₃*(r⁻¹)^5*N) :
    ‖(3*r^2) • u₁ + (3*r^4) • u₂ + r^6 • u₃‖ ≤ (3*B₁+3*B₂+B₃)*r*N := by
  calc
    _ ≤ ‖(3*r^2) • u₁‖ + ‖(3*r^4) • u₂‖ + ‖r^6 • u₃‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (3*r^2)*‖u₁‖+(3*r^4)*‖u₂‖+r^6*‖u₃‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*r^2),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 3*r^4),abs_of_nonneg (by positivity : (0:ℝ) ≤ r^6)]
    _ ≤ (3*r^2)*(B₁*r⁻¹*N)+(3*r^4)*(B₂*(r⁻¹)^3*N)+r^6*(B₃*(r⁻¹)^5*N) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
        (mul_le_mul_of_nonneg_left h₂ (by positivity)))
        (mul_le_mul_of_nonneg_left h₃ (by positivity))
    _ = _ := by field_simp [hr.ne']
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include D hD in

lemma hodge_cube_commutator_global_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        ‖hodgeCubeCommutator A J α hs ht r f‖ ≤
          B*r*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ := by
  obtain ⟨B₁,hB₁,h₁⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 0 (by norm_num)
  obtain ⟨B₂,hB₂,h₂⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 1 (by norm_num)
  obtain ⟨B₃,hB₃,h₃⟩ := hodge_power_commutator_global_bound A J α hs ht D hD 2 (by norm_num)
  refine ⟨3*B₁+3*B₂+B₃,by positivity,fun r hr hr1 f => ?_⟩
  rw [hodgeCubeCommutator_expand]
  simp only [LinearMap.add_apply,LinearMap.smul_apply]
  apply norm_cube_combination_le r hr
  · simpa only [Nat.mul_zero,Nat.zero_add,pow_one] using h₁ r hr hr1 f
  · exact h₂ r hr hr1 f
  · exact h₃ r hr hr1 f
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
lemma hodgeCubeCommutator_apply (r : ℝ) (a : PreL2 A J α hs ht true) :
    hodgeCubeCommutator A J α hs ht r a =
      (hodgeSmoothShift A J α hs ht r ^ 3) (preAntiProjection A J α hs ht a) -
        preAntiProjection A J α hs ht ((hodgeSmoothShift A J α hs ht r ^ 3) a) := rfl
lemma hodgeCubeCommutator_pairing (r : ℝ) (a : PreL2 A J α hs ht true)
    (U : L2 A J α hs ht true) :
    ⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ =
      ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
        (preAntiProjection A J α hs ht a))⟫ -
          ⟪l2AntiProjection A J α hs ht U,
            smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ := by
  rw [hodgeCubeCommutator_apply, map_sub, inner_sub_right, preAntiProjection_smooth,
    l2AntiProjection_self_adjoint]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped RealInnerProductSpace
lemma norm_le_of_dense_pair_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (d : F → E) (hd : DenseRange d) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ f, |⟪v,d f⟫| ≤ B*‖d f‖) : ‖v‖ ≤ B := by
  have hall (y : E) : |⟪v,y⟫| ≤ B*‖y‖ :=
    hd.induction_on y (isClosed_le (continuous_const.inner continuous_id).abs
      (continuous_const.mul continuous_norm)) h
  have hi := hall v
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hi
  by_cases hz : ‖v‖ = 0
  · simpa only [hz] using hB
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

lemma hodge_relative_antiprojection :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ U : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪U,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (preAntiProjection A J α hs ht a))⟫ = 0) →
        ‖l2AntiProjection A J α hs ht U‖ ≤ B*r*‖U‖ := by
  obtain ⟨B,hB,hbound⟩ := hodge_cube_commutator_global_bound A J α hs ht D hD
  refine ⟨B,hB,fun r hr hr1 U hU => ?_⟩
  apply norm_le_of_dense_pair_bound _ _ (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr)
    (B*r*‖U‖) (by positivity)
  intro a
  have he : ⟪l2AntiProjection A J α hs ht U,
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)⟫ =
      -⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫ := by
    rw [hodgeCubeCommutator_pairing,hU,zero_sub,neg_neg]
  calc
    _ = |⟪U,smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)⟫| := by rw [he,abs_neg]
    _ ≤ ‖U‖*‖smoothL2 A J α hs ht true (hodgeCubeCommutator A J α hs ht r a)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖U‖*(B*r*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)‖) := by
      rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht true).norm_map]
      exact mul_le_mul_of_nonneg_left (hbound r hr hr1 a) (norm_nonneg U)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
