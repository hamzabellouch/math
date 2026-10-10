import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGraphSmoothing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothCommutator

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

def hodgeScaleH3Input (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] hodgeEnergy A J α hs ht :=
  (r^2)⁻¹ • ((hodgeWeakSolution A J α hs ht r hr).comp (hodgeResolvent A J α hs ht r))+
    (1-(r^2)⁻¹) • hodgeRegularizedGraph A J α hs ht r hr

lemma hodgeScaleH3Input_spec (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    hodgeGraphResolvent A J α hs ht 1 zero_lt_one (hodgeScaleH3Input A J α hs ht r hr f) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
  have hi : hodgeInclusion A J α hs ht
      (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)) =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  have hu : hodgeGraphResolvent A J α hs ht r hr
      (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)) =
      hodgeRegularizedGraph A J α hs ht r hr f := by
    exact congrArg (hodgeWeakSolution A J α hs ht r hr) hi
  have h := hodgeGraphResolvent_scale_transfer A J α hs ht r hr
    (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f))
  rw [hu] at h
  exact h

lemma hodgeRegularizedGraph_small_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : L2 A J α hs ht true) :
    ‖hodgeRegularizedGraph A J α hs ht r hr f‖ ≤ 2*r⁻¹*‖f‖ := by
  exact (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
    (mul_le_mul_of_nonneg_left
      ((hodgeResolvent_norm_le A J α hs ht r _).trans (hodgeResolvent_norm_le A J α hs ht r f))
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))

lemma hodgeScaleH3Input_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (f : L2 A J α hs ht true) :
    ‖hodgeScaleH3Input A J α hs ht r hr f‖ ≤ 4*(r⁻¹)^3*‖f‖ := by
  let a := (r^2)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (sq_nonneg _)
  have ha1 : 1 ≤ a := by
    apply (one_le_inv₀ (sq_pos_of_pos hr)).mpr
    have : r*r ≤ 1*1 := mul_le_mul hr1 hr1 hr.le zero_le_one
    simpa only [pow_two,one_mul] using this
  have hb : |1-a| ≤ a := by rw [abs_of_nonpos (by linarith)]; linarith
  have hu₂ : ‖hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖ ≤ 2*r⁻¹*‖f‖ :=
    (hodgeWeakSolution_graph_small_bound A J α hs ht r hr hr1 _).trans
      (mul_le_mul_of_nonneg_left (hodgeResolvent_norm_le A J α hs ht r f)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le)))
  change ‖a • hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)+
    (1-a) • hodgeRegularizedGraph A J α hs ht r hr f‖ ≤ _
  calc
    _ ≤ ‖a • hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖+
        ‖(1-a) • hodgeRegularizedGraph A J α hs ht r hr f‖ := norm_add_le _ _
    _ = a*‖hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r f)‖+
        |1-a| *‖hodgeRegularizedGraph A J α hs ht r hr f‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ a*(2*r⁻¹*‖f‖)+a*(2*r⁻¹*‖f‖) := add_le_add (mul_le_mul_of_nonneg_left hu₂ ha)
      (mul_le_mul hb (hodgeRegularizedGraph_small_bound A J α hs ht r hr hr1 f) (norm_nonneg _) ha)
    _ = _ := by dsimp [a]; rw [inv_pow]; ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] in

lemma hodgeRegularization_uniform_local_H1 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 1,
          (∀ f, toDistribution Space (C 6) 1 (L f) =
            hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f)) ∧
          ∀ f, ‖L f‖ ≤ B*r⁻¹*‖f‖ := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  let F := hodgeRawDistribution A J α hs ht D hD p τ
  have hF : ∀ u, MemSobolev 1 2 (F u) := hodgeRawDistribution_H1 A J α hs ht D hD p τ
  let L := realSobolevLift 1 F hF
  have hL := realSobolevLift_spec 1 F hF
  refine ⟨τ,U,hU,hqU,hUD,hτ,2*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeRegularizedGraph A J α hs ht r hr),?_,?_⟩
  · exact fun f => hL _
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeRegularizedGraph A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(2*r⁻¹*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeRegularizedGraph_small_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRegularization_uniform_local_H3 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 3,
          (∀ f, toDistribution Space (C 6) 3 (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^3*‖f‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,L,hL⟩ := exists_hodgeGraphResolvent_H3_lift A J α hs ht D hD p q hq hwq
  refine ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,4*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeScaleH3Input A J α hs ht r hr),?_,?_⟩
  · intro f
    rw [ContinuousLinearMap.comp_apply,hL,hodgeScaleH3Input_spec]
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeScaleH3Input A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(4*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeScaleH3Input_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
