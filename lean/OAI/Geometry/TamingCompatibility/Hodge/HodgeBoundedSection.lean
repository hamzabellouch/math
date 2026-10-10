import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelTestTransform

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scalar_pair_add (f : X → ℝ) (a c b : TwoForm X) :
    (fun x => f x * GeometricAdjoint.pairing J α ht (a+c) b x) =
      (fun x => f x * GeometricAdjoint.pairing J α ht a b x +
        f x * GeometricAdjoint.pairing J α ht c b x) := by
  funext x
  change f x * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (a x+c x) (b x) = _
  erw [MetricForms.pairing_add_left',mul_add]
  rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scalar_pair_smul (f : X → ℝ) (a b : TwoForm X) (c : ℝ) :
    (fun x => f x * GeometricAdjoint.pairing J α ht (c • a) b x) =
      (fun x => c * (f x * GeometricAdjoint.pairing J α ht a b x)) := by
  funext x
  change f x * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (c • a x) (b x) = _
  erw [MetricForms.pairing_smul_left]
  change f x * (c * GeometricAdjoint.pairing J α ht a b x) = _
  ring

def scalarSectionFunctional (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    PreL2 A J α hs ht true →ₗ[ℝ] ℝ where
  toFun a := ∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α
  map_add' a c := by
    change (∫ x, f x * GeometricAdjoint.pairing J α ht (a.val+c.val) b.val x ∂geometricVolume A J α) = _
    rw [scalar_pair_add]
    exact integral_add (bounded_pairing_integrable A J α hs ht a b f hfm hC hf)
      (bounded_pairing_integrable A J α hs ht c b f hfm hC hf)
  map_smul' c a := by
    change (∫ x, f x * GeometricAdjoint.pairing J α ht (c • a.val) b.val x ∂geometricVolume A J α) = _
    rw [scalar_pair_smul,integral_const_mul]
    rfl

def boundedScalarSection (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    L2 A J α hs ht true :=
  (InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm
    ((scalarSectionFunctional A J α hs ht b f hfm C hC hf).extendOfNorm
      (smoothL2 A J α hs ht true).toLinearMap)

lemma boundedScalarSection_norm (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    ‖boundedScalarSection A J α hs ht b f hfm C hC hf‖ ≤ C*‖b‖ := by
  rw [boundedScalarSection,(InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm.norm_map]
  apply LinearMap.opNorm_extendOfNorm_le (smoothL2_dense A J α hs ht true)
    (mul_nonneg hC (norm_nonneg _))
  intro a
  simpa only [scalarSectionFunctional,LinearMap.coe_mk,AddHom.coe_mk,
    LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map,mul_right_comm C] using
      bounded_pairing_integral_bound A J α hs ht a b f hC hf

lemma boundedScalarSection_pairing (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C)
    (a : PreL2 A J α hs ht true) :
    ⟪boundedScalarSection A J α hs ht b f hfm C hC hf,smoothL2 A J α hs ht true a⟫ =
      ∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α := by
  rw [boundedScalarSection,InnerProductSpace.toDual_symm_apply]
  exact LinearMap.extendOfNorm_eq (smoothL2_dense A J α hs ht true)
    ⟨C*‖b‖,fun v => by
      simpa only [scalarSectionFunctional,LinearMap.coe_mk,AddHom.coe_mk,
        LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map,mul_right_comm C] using
        bounded_pairing_integral_bound A J α hs ht v b f hC hf⟩ a

lemma boundedScalarSection_unique (u : L2 A J α hs ht true)
    (b : PreL2 A J α hs ht true) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C)
    (hu : ∀ a : PreL2 A J α hs ht true, ⟪u,smoothL2 A J α hs ht true a⟫ =
      ∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α) :
    u = boundedScalarSection A J α hs ht b f hfm C hC hf := by
  apply ext_inner_right ℝ
  intro v
  refine (smoothL2_dense A J α hs ht true).induction_on v
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  exact (hu a).trans (boundedScalarSection_pairing A J α hs ht b f hfm C hC hf a).symm

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_exists : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(squareMass A x)⁻¹‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (squareMass_inv_smooth A).continuous.continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

def frameMassBound : ℝ := (frameMassBound_exists A).choose
omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_nonneg : 0 ≤ frameMassBound A := (frameMassBound_exists A).choose_spec.1
omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_bound (x : X) : ‖(squareMass A x)⁻¹‖ ≤ frameMassBound A :=
  (frameMassBound_exists A).choose_spec.2 x

include hs hE in
def globalFramePreL2 (p : A.centers) (j : Fin 6) : PreL2 A J α hs ht true :=
  ⟨globalFrame J α ht A E p j,globalFrame_smooth J α ht A E hE hs p j⟩

def frameCoefficient (v : X → FrameSpace A) (p : A.centers) (j : Fin 6) (x : X) : ℝ :=
  (squareMass A x)⁻¹ * v x (p,j)

omit [CompactSpace X] [T2Space X] in
lemma frameCoefficient_measurable (v : X → FrameSpace A)
    (hv : AEStronglyMeasurable v (geometricVolume A J α)) (p : A.centers) (j : Fin 6) :
    AEStronglyMeasurable (frameCoefficient A v p j) (geometricVolume A J α) :=
  (squareMass_inv_smooth A).continuous.aestronglyMeasurable.mul
    ((continuous_apply (p,j)).comp_aestronglyMeasurable hv)

omit [T2Space X] [BorelSpace X] in
lemma frameCoefficient_bound (v : X → FrameSpace A) {V : ℝ}
    (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) (p : A.centers) (j : Fin 6) :
    ∀ᵐ x ∂geometricVolume A J α, ‖frameCoefficient A v p j x‖ ≤ frameMassBound A * V := by
  filter_upwards [hv] with x hx
  rw [frameCoefficient,norm_mul]
  exact mul_le_mul (frameMassBound_bound A x) ((norm_le_pi_norm _ (p,j)).trans hx)
    (norm_nonneg _) (frameMassBound_nonneg A)

def boundedFrameSection (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) :
    L2 A J α hs ht true :=
  ∑ p : A.centers, ∑ j : Fin 6, boundedScalarSection A J α hs ht
    (globalFramePreL2 A J α hs ht E hE p j) (frameCoefficient A v p j)
    (frameCoefficient_measurable A J α v hvm p j) (frameMassBound A*V)
    (mul_nonneg (frameMassBound_nonneg A) hV) (frameCoefficient_bound A J α v hv p j)

lemma boundedFrameSection_norm (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) :
    ‖boundedFrameSection A J α hs ht E hE v hvm V hV hv‖ ≤
      (frameMassBound A * ∑ p : A.centers, ∑ j : Fin 6, ‖globalFramePreL2 A J α hs ht E hE p j‖)*V := by
  unfold boundedFrameSection
  calc
    _ ≤ ∑ p : A.centers, ∑ j : Fin 6, (frameMassBound A*V)*‖globalFramePreL2 A J α hs ht E hE p j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact boundedScalarSection_norm _ _ _ _ _ _ _ _ _ _ _
    _ = _ := by simp_rw [← Finset.mul_sum]; ring

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_coefficient_sum (a : TwoForm X) (v : X → FrameSpace A) (x : X) :
    framePairing A J α ht E a x (v x) =
      ∑ p : A.centers, ∑ j : Fin 6,
        frameCoefficient A v p j x * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x := by
  simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold frameCoefficient
  ring

lemma boundedFrameSection_pairing (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V)
    (a : PreL2 A J α hs ht true) :
    ⟪boundedFrameSection A J α hs ht E hE v hvm V hV hv,smoothL2 A J α hs ht true a⟫ =
      ∫ x, framePairing A J α ht E a.val x (v x) ∂geometricVolume A J α := by
  have hi (p : A.centers) (j : Fin 6) : Integrable (fun x => frameCoefficient A v p j x *
      GeometricAdjoint.pairing J α ht a.val (globalFrame J α ht A E p j) x) (geometricVolume A J α) :=
    bounded_pairing_integrable A J α hs ht a (globalFramePreL2 A J α hs ht E hE p j) _
      (frameCoefficient_measurable A J α v hvm p j) (mul_nonneg (frameMassBound_nonneg A) hV)
      (frameCoefficient_bound A J α v hv p j)
  simp_rw [framePairing_coefficient_sum]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun j _ => hi p j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  unfold boundedFrameSection
  simp_rw [sum_inner,boundedScalarSection_pairing]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
