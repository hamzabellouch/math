import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothLaplacian

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_differential_inverse (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true
      (a+r^2 • hodgeLaplacian A J α hs ht a)) = smoothL2 A J α hs ht true a := by
  have he : hodgeWeakSolution A J α hs ht r hr (smoothL2 A J α hs ht true
      (a+r^2 • hodgeLaplacian A J α hs ht a)) = hodgeSmooth A J α hs ht a := by
    apply hodgeWeakSolution_unique A J α hs ht r hr
    intro v
    rw [map_add,map_smul,inner_add_left,real_inner_smul_left,hodgeLaplacian_green_weak]
    rfl
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,he]
  rfl

lemma hodgeResolvent_smooth_error (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true a)-smoothL2 A J α hs ht true a =
      -(r^2) • hodgeResolvent A J α hs ht r
        (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)) := by
  have h := hodgeResolvent_differential_inverse A J α hs ht r hr a
  rw [map_add,map_smul,map_add,map_smul] at h
  rw [neg_smul]
  exact eq_neg_iff_add_eq_zero.mpr (by rw [sub_add_eq_add_sub,h,sub_self])

lemma hodgeResolvent_smooth_error_bound (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    ‖hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true a)-smoothL2 A J α hs ht true a‖ ≤
      r^2 * ‖smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)‖ := by
  rw [hodgeResolvent_smooth_error A J α hs ht r hr a,norm_smul,Real.norm_eq_abs,abs_neg,
    abs_of_nonneg (sq_nonneg r)]
  exact mul_le_mul_of_nonneg_left (hodgeResolvent_norm_le A J α hs ht r _) (sq_nonneg r)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set HilbertSobolev ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraphResolvent_all_orders (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ (f : PreL2 A J α hs ht true) (n : ℕ),
        MemSobolevLoc V n (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f))) := by
  induction j with
  | zero =>
    refine ⟨U,hU,hq,Subset.rfl,fun f n => ?_⟩
    simp only [pow_zero,one_apply_eq_self]
    rw [hodgeRawDistribution_smooth]
    exact schwartz_memSobolevLoc _ n U
  | succ j ih =>
    obtain ⟨V,hV,hqV,hVU,hall⟩ := ih
    obtain ⟨W,hW,hqW,hWV,hgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
      hV (hVU.trans hUD) (fun z hz => hτ z (hVU hz)) q hqV r hr
    refine ⟨W,hW,hqW,hWV.trans hVU,fun f n => ?_⟩
    rw [pow_succ',mul_apply_eq_comp]
    exact (hgain n _ (hall f n)).mono (by simp)

lemma hodgeGraphResolvent_local_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧ ∃ g : Space →ᵇ C 6,
      ContDiff ℝ ∞ (g : Space → C 6) ∧ ∀ χ : 𝓢(Space,ℂ),
        HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f))) =
          smulLeftCLM (C 6) χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨W,hW,hqW,hWU,hall⟩ :=
    hodgeGraphResolvent_all_orders A J α hs ht D hD p τ hU hUD hτ q hq r hr j
  obtain ⟨V,hV,hqV,hVW,g,hg,he⟩ := exists_local_smooth_representative hW hqW (hall f)
  exact ⟨V,hV,hqV,hVW.trans hWU,g,hg,he⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
