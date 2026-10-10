import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairAllTests

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

theorem hodgeGraphResolvent_smooth (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b =
      (hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f) := by
  classical
  choose V hV hxV w hw using hodge_exists_weak_patch A J α hs ht D hD r hr j f
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply hodge_glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) _ (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [T2Space X] in
lemma hodgeResolvent_injective (r : ℝ) (hr : 0 < r) :
    Function.Injective (hodgeResolvent A J α hs ht r) := by
  intro f g h
  apply ext_inner_right ℝ
  have hsym (u v : L2 A J α hs ht true) :
      ⟪hodgeResolvent A J α hs ht r u,v⟫ = ⟪u,hodgeResolvent A J α hs ht r v⟫ :=
    hodgeResolvent_symmetric A J α hs ht r u v
  have he : (fun y : L2 A J α hs ht true => ⟪f,y⟫) = (fun y => ⟪g,y⟫) :=
    (smoothL2_dense A J α hs ht true).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (by
      funext a
      change ⟪f,smoothL2 A J α hs ht true a⟫ = ⟪g,smoothL2 A J α hs ht true a⟫
      rw [← hodgeResolvent_smoothShift A J α hs ht r hr a,
        ← hsym,← hsym,h])
  exact congrFun he
omit [T2Space X] in
lemma hodgeRegularization_injective (r : ℝ) (hr : 0 < r) :
    Function.Injective (hodgeRegularization A J α hs ht r) := by
  intro f g h
  change hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f)) =
    hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r g)) at h
  exact hodgeResolvent_injective A J α hs ht r hr
    (hodgeResolvent_injective A J α hs ht r hr (hodgeResolvent_injective A J α hs ht r hr h))
omit [T2Space X] in
lemma hodgeGraphResolvent_inclusion_power (r : ℝ) (hr : 0 < r) (j : ℕ)
    (u : hodgeEnergy A J α hs ht) :
    hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j) u) =
      (hodgeResolvent A J α hs ht r ^ j) (hodgeInclusion A J α hs ht u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',pow_succ']
    change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr
      (hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j) u))) = _
    rw [ih,hodgeResolvent_eq A J α hs ht r hr]
    rfl
include D hD in
lemma hodgeRegularization_smooth (r : ℝ) (hr : 0 < r) (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true, smoothL2 A J α hs ht true b =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f) := by
  obtain ⟨b,hb⟩ := hodgeGraphResolvent_smooth A J α hs ht D hD r hr 3 f
  refine ⟨b,?_⟩
  have h := congrArg (hodgeInclusion A J α hs ht) hb
  simpa only [hodgeInclusion_smooth,hodgeGraphResolvent_inclusion_power,hodgeRegularization] using h
include D hD in

lemma hodgeSmoothShift_cube_dense (r : ℝ) (hr : 0 < r) :
    DenseRange (fun a : PreL2 A J α hs ht true =>
      smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) a)) := by
  apply (smoothL2_dense A J α hs ht true).mono
  rintro _ ⟨f,rfl⟩
  obtain ⟨b,hb⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr f
  refine ⟨b,?_⟩
  apply hodgeRegularization_injective A J α hs ht r hr
  rw [hodgeRegularization_smoothShift_cube A J α hs ht r hr,hb]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricAdjoint MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
local instance (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

lemma jAction_pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : TwoForm X) (x : X) :
    pairing J α ht (TamingCompatibility.jAction J a) (TamingCompatibility.jAction J b) x =
      pairing J α ht a b x := by
  let L : TangentSpace Model x ≃L[ℝ] TangentSpace Model x :=
    (LinearEquiv.ofBijective (J.endomorphism x).toLinearMap
      ⟨J.injective x,J.surjective x⟩).toContinuousLinearEquiv
  exact MetricForms.pairing_two_comp (pointMetric J α ht x) (pointMetric J α ht x) L
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by change Module.finrank ℝ Space = 4; simp [Space]) (a x) (b x)

namespace GeometricHilbert
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def preJAction : PreL2 A J α hs ht true →ₗᵢ[ℝ] PreL2 A J α hs ht true where
  toFun a := ⟨TamingCompatibility.jAction J a.val,IsSmooth.jAction a.property J⟩
  map_add' a b := Subtype.ext (TamingCompatibility.jAction_add J a.val b.val)
  map_smul' c a := Subtype.ext (TamingCompatibility.jAction_smul J c a.val)
  norm_map' a := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [preL2_norm_sq,preL2_norm_sq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (jAction_pairing J α ht a.val a.val)

lemma preJAction_square (a : PreL2 A J α hs ht true) :
    preJAction A J α hs ht (preJAction A J α hs ht a) = a :=
  Subtype.ext (jAction_involutive J a.val)

def l2JAction : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  ((smoothL2 A J α hs ht true).toContinuousLinearMap.comp
    (preJAction A J α hs ht).toContinuousLinearMap).extend
      (smoothL2 A J α hs ht true).toContinuousLinearMap

@[simp] lemma l2JAction_smooth (a : PreL2 A J α hs ht true) :
    l2JAction A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true (preJAction A J α hs ht a) := by
  exact ContinuousLinearMap.extend_eq _ (smoothL2_dense A J α hs ht true)
    (smoothL2 A J α hs ht true).isometry.isUniformInducing a

lemma l2JAction_square (a : L2 A J α hs ht true) :
    l2JAction A J α hs ht (l2JAction A J α hs ht a) = a := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq ((l2JAction A J α hs ht).continuous.comp
      (l2JAction A J α hs ht).continuous) continuous_id) ?_
  intro b
  rw [l2JAction_smooth,l2JAction_smooth,preJAction_square]

lemma l2JAction_norm (a : L2 A J α hs ht true) : ‖l2JAction A J α hs ht a‖ = ‖a‖ := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq (l2JAction A J α hs ht).continuous.norm continuous_norm) ?_
  intro b
  rw [l2JAction_smooth,(smoothL2 A J α hs ht true).norm_map,
    (preJAction A J α hs ht).norm_map,(smoothL2 A J α hs ht true).norm_map]

lemma l2JAction_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2JAction A J α hs ht a,b⟫ = ⟪a,l2JAction A J α hs ht b⟫ := by
  let S : L2 A J α hs ht true →ₗᵢ[ℝ] L2 A J α hs ht true :=
    ⟨(l2JAction A J α hs ht).toLinearMap,l2JAction_norm A J α hs ht⟩
  conv_lhs => rw [← l2JAction_square A J α hs ht b]
  exact S.inner_map_map a (l2JAction A J α hs ht b)

def l2AntiProjection : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - l2JAction A J α hs ht)

@[simp] lemma l2AntiProjection_apply (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht a = (1/2:ℝ) • (a-l2JAction A J α hs ht a) := rfl

lemma l2AntiProjection_smooth (a : PreL2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (smoothL2 A J α hs ht true a) =
      smoothL2 A J α hs ht true ⟨antiInvariantPart J a.val,IsSmooth.antiInvariantPart a.property J⟩ := by
  rw [l2AntiProjection_apply,l2JAction_smooth,← map_sub,← map_smul]
  rfl

lemma l2AntiProjection_square (a : L2 A J α hs ht true) :
    l2AntiProjection A J α hs ht (l2AntiProjection A J α hs ht a) =
      l2AntiProjection A J α hs ht a := by
  simp only [l2AntiProjection_apply,map_smul,map_sub,l2JAction_square]
  module

lemma l2AntiProjection_self_adjoint (a b : L2 A J α hs ht true) :
    ⟪l2AntiProjection A J α hs ht a,b⟫ = ⟪a,l2AntiProjection A J α hs ht b⟫ := by
  simp only [l2AntiProjection_apply,real_inner_smul_left,real_inner_smul_right,
    inner_sub_left,inner_sub_right,l2JAction_self_adjoint]

lemma l2AntiProjection_norm (a : L2 A J α hs ht true) :
    ‖l2AntiProjection A J α hs ht a‖ ≤ ‖a‖ := by
  rw [l2AntiProjection_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have h := norm_sub_le a (l2JAction A J α hs ht a)
  rw [l2JAction_norm] at h
  linarith

lemma l2AntiProjectionStar (a : L2 A J α hs ht true) :
    l2Star A J α hs ht (l2AntiProjection A J α hs ht a) = l2AntiProjection A J α hs ht a := by
  refine (smoothL2_dense A J α hs ht true).induction_on a
    (isClosed_eq ((l2Star A J α hs ht).continuous.comp
      (l2AntiProjection A J α hs ht).continuous) (l2AntiProjection A J α hs ht).continuous) ?_
  intro b
  rw [l2AntiProjection_smooth]
  let c : PreL2 A J α hs ht true :=
    ⟨antiInvariantPart J b.val,IsSmooth.antiInvariantPart b.property J⟩
  change l2Star A J α hs ht (smoothL2 A J α hs ht true c) =
    smoothL2 A J α hs ht true c
  rw [l2Star_smooth]
  exact congrArg (smoothL2 A J α hs ht true)
    (Subtype.ext (starTwo_antiInvariant J α ht b.val))

end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
