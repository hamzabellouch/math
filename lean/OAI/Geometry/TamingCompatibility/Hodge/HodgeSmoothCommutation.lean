import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeConvergence
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothInverse

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeSmoothShift_commute (r s : ℝ) :
    Commute (hodgeSmoothShift A J α hs ht r) (hodgeSmoothShift A J α hs ht s) := by
  change (_ : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true) = _
  simp only [hodgeSmoothShift,add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  module

omit [T2Space X] in
lemma hodgeSmoothShift_cubes_commute (r s : ℝ) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r^3) ((hodgeSmoothShift A J α hs ht s^3) a) =
      (hodgeSmoothShift A J α hs ht s^3) ((hodgeSmoothShift A J α hs ht r^3) a) := by
  have h := ((hodgeSmoothShift_commute A J α hs ht r s).pow_pow 3 3).eq
  exact congrArg (fun L : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true => L a) h

lemma hodgeSmoothInverse_commute (r : ℝ) (hr : 0 < r) (s : ℝ)
    (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht s^3) (hodgeSmoothInverse A J α hs ht D hD r hr a) =
      hodgeSmoothInverse A J α hs ht D hD r hr ((hodgeSmoothShift A J α hs ht s^3) a) := by
  apply (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr).injective
  dsimp only
  rw [hodgeSmoothShift_cubes_commute A J α hs ht r s,
    hodgeSmoothInverse_right,hodgeSmoothInverse_right]

def hodgeSmoothFamily (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  if hr : 0 < r then (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap else LinearMap.id

lemma hodgeSmoothFamily_spec (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true (hodgeSmoothFamily A J α hs ht D hD r a) =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true a) := by
  simp only [hodgeSmoothFamily,dite_eq_left hr,LinearEquiv.coe_coe,hodgeSmoothInverse_spec]

lemma hodgeSmoothFamily_graph (r : ℝ) (hr : 0 < r) (s : ℝ)
    (a : PreL2 A J α hs ht true) :
    smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht s^3)
      (hodgeSmoothFamily A J α hs ht D hD r a)) =
      hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht s^3) a)) := by
  simp only [hodgeSmoothFamily,dite_eq_left hr,LinearEquiv.coe_coe,
    hodgeSmoothInverse_commute,hodgeSmoothInverse_spec]

omit [T2Space X] in
lemma hodgeRegularization_twice_tendsto (a : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeRegularization A J α hs ht r (hodgeRegularization A J α hs ht r a))
      (𝓝[>] 0) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun r : ℝ => 2*‖hodgeRegularization A J α hs ht r a-a‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((hodgeRegularization_tendsto A J α hs ht a).sub (tendsto_const_nhds (x:=a))).norm.const_mul 2)
  apply squeeze_zero (fun r => norm_nonneg _) _ h
  intro r
  have hb := hodgeRegularization_norm_le A J α hs ht r (hodgeRegularization A J α hs ht r a-a)
  rw [map_sub] at hb
  have ht := norm_add_le (hodgeRegularization A J α hs ht r (hodgeRegularization A J α hs ht r a)-
    hodgeRegularization A J α hs ht r a) (hodgeRegularization A J α hs ht r a-a)
  rw [sub_add_sub_cancel] at ht
  linarith
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def evaluationApply : L2 A J α hs ht true →L[ℝ] C(MetricUnit g,ℝ) :=
by
  let hex := (isCompact_univ : IsCompact (Set.univ : Set (MetricUnit g))).exists_bound_of_continuousOn
    (f := C.evaluation g) (C.evaluation_continuous g).continuousOn
  let K := hex.choose
  have hK := hex.choose_spec
  exact LinearMap.mkContinuous
    { toFun := fun f => ⟨fun u => C.evaluation g u f,
        (C.evaluation_continuous g).clm_apply continuous_const⟩
      map_add' := fun f h => by ext u; exact map_add (C.evaluation g u) f h
      map_smul' := fun c f => by ext u; exact map_smul (C.evaluation g u) c f }
    (max K 0) (fun f => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (le_max_right _ _) (norm_nonneg _))).mpr
      intro u
      exact ((C.evaluation g u).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right ((hK u (mem_univ u)).trans (le_max_left _ _))
          (norm_nonneg f)))

lemma evaluationApply_smooth (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.evaluationApply g f = smoothUnitEvaluation J g a := by
  ext u
  exact C.evaluation_smooth g u f a ha
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

lemma hodgeSmoothFamily_evaluation (r : ℝ) (hr : 0 < r)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (C : HodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one)
    (a : PreL2 A J α hs ht true) :
    smoothUnitEvaluation J g (hodgeSmoothFamily A J α hs ht D hD r a) =
      C.evaluationApply g (hodgeRegularization A J α hs ht r
        (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a))) := by
  rw [← hodgeSmoothFamily_graph A J α hs ht D hD r hr 1 a]
  exact (C.evaluationApply_smooth g _ _
    (hodgeRegularization_smoothShift_cube A J α hs ht 1 zero_lt_one _)).symm

lemma hodgeSmoothFamily_twice_evaluation (r : ℝ) (hr : 0 < r)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (C : HodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one)
    (a : PreL2 A J α hs ht true) :
    smoothUnitEvaluation J g
      (hodgeSmoothFamily A J α hs ht D hD r (hodgeSmoothFamily A J α hs ht D hD r a)) =
      C.evaluationApply g (hodgeRegularization A J α hs ht r
        (hodgeRegularization A J α hs ht r
          (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a)))) := by
  rw [hodgeSmoothFamily_evaluation A J α hs ht D hD r hr g C,
    hodgeSmoothFamily_graph A J α hs ht D hD r hr 1 a]

lemma hodgeSmoothFamily_uniform_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => smoothUnitEvaluation J g (hodgeSmoothFamily A J α hs ht D hD r a))
      (𝓝[>] 0) (𝓝 (smoothUnitEvaluation J g a)) := by
  let C := hodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one
  let b := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a)
  have he : C.evaluationApply g b = smoothUnitEvaluation J g a :=
    C.evaluationApply_smooth g b a (hodgeRegularization_smoothShift_cube A J α hs ht 1 zero_lt_one a)
  have hl := (C.evaluationApply g).continuous.tendsto b |>.comp
    (hodgeRegularization_tendsto A J α hs ht b)
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hodgeSmoothFamily_evaluation A J α hs ht D hD r hr g C a).symm

lemma hodgeSmoothFamily_twice_uniform_tendsto
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (a : PreL2 A J α hs ht true) :
    Tendsto (fun r : ℝ => smoothUnitEvaluation J g
      (hodgeSmoothFamily A J α hs ht D hD r (hodgeSmoothFamily A J α hs ht D hD r a)))
      (𝓝[>] 0) (𝓝 (smoothUnitEvaluation J g a)) := by
  let C := hodgeSmoothingCover A J α hs ht D hD 1 zero_lt_one
  let b := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht 1^3) a)
  have he : C.evaluationApply g b = smoothUnitEvaluation J g a :=
    C.evaluationApply_smooth g b a (hodgeRegularization_smoothShift_cube A J α hs ht 1 zero_lt_one a)
  have hl := (C.evaluationApply g).continuous.tendsto b |>.comp
    (hodgeRegularization_twice_tendsto A J α hs ht b)
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hodgeSmoothFamily_twice_evaluation A J α hs ht D hD r hr g C a).symm
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
