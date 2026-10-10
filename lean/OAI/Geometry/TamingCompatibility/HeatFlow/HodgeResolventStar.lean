import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalEvaluation

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeWeakSolution_unique (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true)
    (u : hodgeEnergy A J α hs ht)
    (hu : ∀ v : hodgeEnergy A J α hs ht,
      ⟪hodgeInclusion A J α hs ht u,hodgeInclusion A J α hs ht v⟫ +
        r^2*⟪hodgeWeakDerivative A J α hs ht u,hodgeWeakDerivative A J α hs ht v⟫ =
          ⟪f,hodgeInclusion A J α hs ht v⟫) :
    hodgeWeakSolution A J α hs ht r hr f = u := by
  let w := hodgeWeakSolution A J α hs ht r hr f
  let i := hodgeInclusion A J α hs ht
  let D := hodgeWeakDerivative A J α hs ht
  have he := hodgeWeakSolution_identity A J α hs ht r hr f (w-u)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at he
  have hu' := hu (w-u)
  have hz : ⟪i (w-u),i (w-u)⟫ +r^2*⟪D (w-u),D (w-u)⟫ = 0 := by
    rw [map_sub,map_sub,inner_sub_left,inner_sub_left]
    change ⟪i w,i w-i u⟫ +r^2*⟪D w,D w-D u⟫ = ⟪f,i w-i u⟫ at he
    change ⟪i u,i w-i u⟫ +r^2*⟪D u,D w-D u⟫ = ⟪f,i w-i u⟫ at hu'
    linarith
  have hnon : 0 ≤ r^2*⟪D (w-u),D (w-u)⟫ := mul_nonneg (sq_nonneg _) real_inner_self_nonneg
  have hh : ⟪i (w-u),i (w-u)⟫ = 0 := le_antisymm (by linarith) real_inner_self_nonneg
  have hzero : i (w-u) = 0 := inner_self_eq_zero.mp hh
  apply hodgeInclusion_injective A J α hs ht
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hzero)

lemma hodgeWeakSolution_star (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr (l2Star A J α hs ht f) =
      hodgeDomainStar A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) := by
  apply hodgeWeakSolution_unique A J α hs ht r hr
  intro v
  rw [hodgeInclusion_star,l2Star_self_adjoint,hodgeDerivative_star_adjoint]
  have h := hodgeWeakSolution_identity A J α hs ht r hr f (hodgeDomainStar A J α hs ht v)
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply] at h
  simpa only [hodgeInclusion_star,l2Star_self_adjoint] using h

lemma hodgeResolvent_star (r : ℝ) (f : L2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeResolvent A J α hs ht r f) := by
  by_cases hr : 0 < r
  · rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,hodgeWeakSolution_star,hodgeInclusion_star]
  · simp only [hodgeResolvent,dite_eq_right hr,one_apply_eq_self]

lemma hodgeRegularization_star (r : ℝ) (f : L2 A J α hs ht true) :
    hodgeRegularization A J α hs ht r (l2Star A J α hs ht f) =
      l2Star A J α hs ht (hodgeRegularization A J α hs ht r f) := by
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
    (hodgeResolvent A J α hs ht r (l2Star A J α hs ht f))) =
      l2Star A J α hs ht (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r
        (hodgeResolvent A J α hs ht r f)))
  rw [hodgeResolvent_star,hodgeResolvent_star,hodgeResolvent_star]
end TamingCompatibility.GeometricHilbert

end

end OAI
