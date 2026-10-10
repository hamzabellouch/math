import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalSmooth

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

def preAntiProjection : PreL2 A J α hs ht true →L[ℝ] PreL2 A J α hs ht true :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - (preJAction A J α hs ht).toContinuousLinearMap)

lemma preAntiProjection_apply (a : PreL2 A J α hs ht true) :
    preAntiProjection A J α hs ht a =
      ⟨antiInvariantPart J a.val,IsSmooth.antiInvariantPart a.property J⟩ := rfl

lemma preAntiProjection_smooth (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (preAntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) :=
  (l2AntiProjection_smooth A J α hs ht a).symm

lemma preAntiProjection_self_adjoint (a b : PreL2 A J α hs ht true) :
    ⟪preAntiProjection A J α hs ht a,b⟫ = ⟪a,preAntiProjection A J α hs ht b⟫ := by
  have h := l2AntiProjection_self_adjoint A J α hs ht
    (smoothL2 A J α hs ht true a) (smoothL2 A J α hs ht true b)
  rw [← preAntiProjection_smooth,← preAntiProjection_smooth] at h
  simpa only [(smoothL2 A J α hs ht true).inner_map_map] using h

lemma hodgeLaplacian_power_symmetric (k : ℕ) (a b : PreL2 A J α hs ht true) :
    ⟪((hodgeLaplacian A J α hs ht)^k) a,b⟫ =
      ⟪a,((hodgeLaplacian A J α hs ht)^k) b⟫ := by
  have hd (u v : PreL2 A J α hs ht true) :
      ⟪hodgeLaplacian A J α hs ht u,v⟫ = ⟪u,hodgeLaplacian A J α hs ht v⟫ := by
    simpa only [(smoothL2 A J α hs ht true).inner_map_map] using
      hodgeLaplacian_symmetric A J α hs ht u v
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    calc
      _ = ⟪hodgeLaplacian A J α hs ht (((hodgeLaplacian A J α hs ht)^k) a),b⟫ := by
        rw [pow_succ']; rfl
      _ = ⟪((hodgeLaplacian A J α hs ht)^k) a,hodgeLaplacian A J α hs ht b⟫ := hd _ _
      _ = ⟪a,((hodgeLaplacian A J α hs ht)^k) (hodgeLaplacian A J α hs ht b)⟫ := ih _ _
      _ = _ := by rw [pow_succ]; rfl

def hodgePowerCommutator (k : ℕ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  ((hodgeLaplacian A J α hs ht)^k).comp (preAntiProjection A J α hs ht).toLinearMap -
    (preAntiProjection A J α hs ht).toLinearMap.comp ((hodgeLaplacian A J α hs ht)^k)

lemma hodgePowerCommutator_apply (k : ℕ) (a : PreL2 A J α hs ht true) :
    hodgePowerCommutator A J α hs ht k a =
      ((hodgeLaplacian A J α hs ht)^k) (preAntiProjection A J α hs ht a) -
        preAntiProjection A J α hs ht (((hodgeLaplacian A J α hs ht)^k) a) := rfl

lemma hodgePowerCommutator_skew (k : ℕ) (a b : PreL2 A J α hs ht true) :
    ⟪hodgePowerCommutator A J α hs ht k a,b⟫ =
      -⟪a,hodgePowerCommutator A J α hs ht k b⟫ := by
  rw [hodgePowerCommutator_apply,hodgePowerCommutator_apply,inner_sub_left,inner_sub_right,
    hodgeLaplacian_power_symmetric,preAntiProjection_self_adjoint,
    preAntiProjection_self_adjoint,← hodgeLaplacian_power_symmetric]
  ring

lemma hodgeRegularizedGraph_smoothShift_cube (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    hodgeRegularizedGraph A J α hs ht r hr
      (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) =
        hodgeSmooth A J α hs ht a := by
  apply hodgeInclusion_injective A J α hs ht
  rw [hodgeRegularizedGraph_inclusion,hodgeInclusion_smooth,
    hodgeRegularization_smoothShift_cube A J α hs ht r hr]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped RealInnerProductSpace
lemma linmap_shift_cube {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : E →ₗ[ℝ] E) (r : ℝ) :
    (LinearMap.id + r^2 • d)^3 = LinearMap.id +
      (3*r^2) • d + (3*r^4) • d^2 + r^6 • d^3 := by
  simp only [pow_succ,pow_zero,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
    Module.End.one_eq_id]
  module
lemma linmap_shift_cube_commutator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d p : E →ₗ[ℝ] E) (r : ℝ) :
    ((LinearMap.id + r^2 • d)^3).comp p - p.comp ((LinearMap.id + r^2 • d)^3) =
      (3*r^2) • (d.comp p - p.comp d) +
      (3*r^4) • ((d^2).comp p - p.comp (d^2)) +
      r^6 • ((d^3).comp p - p.comp (d^3)) := by
  rw [linmap_shift_cube]
  simp only [LinearMap.add_comp,LinearMap.comp_add,LinearMap.smul_comp,
    LinearMap.comp_smul,LinearMap.id_comp,LinearMap.comp_id]
  module
end TamingCompatibility
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def hodgeCubeCommutator (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  ((hodgeSmoothShift A J α hs ht r)^3).comp (preAntiProjection A J α hs ht).toLinearMap -
    (preAntiProjection A J α hs ht).toLinearMap.comp ((hodgeSmoothShift A J α hs ht r)^3)

lemma hodgeCubeCommutator_expand (r : ℝ) : hodgeCubeCommutator A J α hs ht r =
    (3*r^2) • hodgePowerCommutator A J α hs ht 1 +
      (3*r^4) • hodgePowerCommutator A J α hs ht 2 +
      r^6 • hodgePowerCommutator A J α hs ht 3 := by
  simpa only [hodgeCubeCommutator,hodgePowerCommutator,hodgeSmoothShift,pow_one] using
    linmap_shift_cube_commutator (hodgeLaplacian A J α hs ht)
      (preAntiProjection A J α hs ht).toLinearMap r

lemma hodgeCubeCommutator_skew (r : ℝ) (a b : PreL2 A J α hs ht true) :
    ⟪hodgeCubeCommutator A J α hs ht r a,b⟫ = -⟪a,hodgeCubeCommutator A J α hs ht r b⟫ := by
  rw [hodgeCubeCommutator_expand]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,hodgePowerCommutator_skew]
  ring
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

lemma hodgeGraphResolvent_raw_H3 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ u : hodgeEnergy A J α hs ht, MemSobolevLoc V 3
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU 1 zero_lt_one
  refine ⟨τ,W,hW,hqW,hWU.trans hUD,fun z hz => hτ z (hWU hz),?_⟩
  intro u
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) U
  simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply]
    using hWgain 1 u (by simpa only [Nat.cast_one] using h₁)

lemma exists_hodgeGraphResolvent_H3_lift (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ L : hodgeEnergy A J α hs ht →L[ℝ] H Space (C 6) 3,
        ∀ u, toDistribution Space (C 6) 3 (L u) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeGraphResolvent_raw_H3 A J α hs ht D hD p q hq hwq
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let F : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,C 6) :=
    ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
      ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeGraphResolvent A J α hs ht 1 zero_lt_one))
  have hF : ∀ u, MemSobolev 3 2 (F u) := fun u => hreg u χ hχc hχV
  refine ⟨τ,χ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_,
    realSobolevLift 3 F hF,realSobolevLift_spec 3 F hF⟩
  intro z hz
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
