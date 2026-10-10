import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothSpatial

namespace OAI

section

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
variable {V E X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
  {μ : Measure X}

def lpEncode (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ) :
    V →ₗ[ℝ] Lp E 2 μ where
  toFun v := (hm v).toLp (φ v)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(hm (v+w)).coeFn_toLp,(hm v).coeFn_toLp,(hm w).coeFn_toLp,
      Lp.coeFn_add ((hm v).toLp (φ v)) ((hm w).toLp (φ w))] with x hx hv hw ha
    rw [hx,ha,Pi.add_apply,hv,hw]
    exact congrFun (φ.map_add v w) x
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(hm (c • v)).coeFn_toLp,(hm v).coeFn_toLp,
      Lp.coeFn_smul c ((hm v).toLp (φ v))] with x hx hv ha
    simp only [RingHom.id_apply] at *
    rw [hx,ha,Pi.smul_apply,hv]
    exact congrFun (φ.map_smul c v) x

lemma lpEncode_inner (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ)
    (v w : V) :
    ⟪lpEncode φ hm v,lpEncode φ hm w⟫ = ∫ x, ⟪φ v x,φ w x⟫ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hm v).coeFn_toLp,(hm w).coeFn_toLp] with x hv hw
  change ⟪(hm v).toLp (φ v) x,(hm w).toLp (φ w) x⟫ = _
  rw [hv,hw]

def lpEncodeIsometry (φ : V →ₗ[ℝ] (X → E)) (hm : ∀ v, MemLp (φ v) 2 μ)
    (hi : ∀ v w, (∫ x, ⟪φ v x,φ w x⟫ ∂μ) = ⟪v,w⟫) : V →ₗᵢ[ℝ] Lp E 2 μ where
  __ := lpEncode φ hm
  norm_map' v := by
    have h : ‖lpEncode φ hm v‖^2 = ‖v‖^2 := by
      rw [← real_inner_self_eq_norm_sq,lpEncode_inner,hi,real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg (lpEncode φ hm v),norm_nonneg v]

variable [CompleteSpace E]
def isometryFromCompletion (f : V →ₗᵢ[ℝ] E) : UniformSpace.Completion V →ₗᵢ[ℝ] E where
  __ := f.toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' v := by
    induction v using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (f.toContinuousLinearMap.fromCompletion.continuous.norm) continuous_norm
    | ih v =>
      change ‖f.toContinuousLinearMap.fromCompletion (v : UniformSpace.Completion V)‖ = _
      rw [ContinuousLinearMap.fromCompletion_apply_coe,UniformSpace.Completion.norm_coe]
      exact f.norm_map v

lemma isometryFromCompletion_coe (f : V →ₗᵢ[ℝ] E) (v : V) :
    isometryFromCompletion f (v : UniformSpace.Completion V) = f v :=
  f.toContinuousLinearMap.fromCompletion_apply_coe v

end TamingCompatibility.GeometricHilbert

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization HodgeFrame MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

abbrev HilbertFrame := EuclideanSpace ℝ (A.centers × Fin 6)

def normalizedFrameEncode (x : X) : MetricForms.Form Space 2 →L[ℝ] HilbertFrame A :=
  (Real.sqrt (squareMass A x))⁻¹ •
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : A.centers × Fin 6 => ℝ)).symm.toContinuousLinearMap ∘L
      frameEncode J α ht A E x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_apply (a : TwoForm X) (x : X) :
    normalizedFrameEncode A J α ht E x (a x) =
      (Real.sqrt (squareMass A x))⁻¹ • WithLp.toLp 2 (frameEncode J α ht A E x (a x)) := rfl

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_inner (a b : TwoForm X) (x : X) :
    ⟪normalizedFrameEncode A J α ht E x (a x),normalizedFrameEncode A J α ht E x (b x)⟫ =
      GeometricAdjoint.pairing J α ht a b x := by
  have hsq : ((Real.sqrt (squareMass A x))⁻¹)^2 = (squareMass A x)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (squareMass_pos A x).le]
  rw [← framePairing_encode A J α ht E hE a b x]
  simp only [normalizedFrameEncode_apply,inner_smul_left,inner_smul_right,
    PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  rw [← mul_assoc,← pow_two,hsq]
  simp only [framePairing,FunLike.coe_smul,Pi.smul_apply,smul_eq_mul,
    _root_.sum_apply,ContinuousLinearMap.proj_apply,frameEncode_apply]
  rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  ring

include hs hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (fun x => normalizedFrameEncode A J α ht E x (a x)) := by
  have hroot : Continuous (fun x => (Real.sqrt (squareMass A x))⁻¹) :=
    ((squareMass_smooth A).continuous.sqrt).inv₀
      (fun x => (Real.sqrt_pos.mpr (squareMass_pos A x)).ne')
  exact hroot.smul ((PiLp.continuous_toLp 2 (fun _ : A.centers × Fin 6 => ℝ)).comp
    (frameEncode_section_smooth J α ht A E hE hs a ha).continuous)

def smoothFrameEncode : PreL2 A J α hs ht true →ₗ[ℝ] (X → HilbertFrame A) where
  toFun a x := normalizedFrameEncode A J α ht E x (a.val x)
  map_add' a b := by funext x; exact map_add _ _ _
  map_smul' c a := by
    funext x
    change normalizedFrameEncode A J α ht E x (c • a.val x) =
      c • normalizedFrameEncode A J α ht E x (a.val x)
    exact map_smul _ _ _

include hE in
lemma smoothFrameEncode_memLp (a : PreL2 A J α hs ht true) :
    MemLp (smoothFrameEncode A J α hs ht E a) 2 (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (normalizedFrameEncode_continuous A J α hs ht E hE a.val a.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
omit [T2Space X] in
lemma smoothFrameEncode_inner_integral (a b : PreL2 A J α hs ht true) :
    (∫ x, ⟪smoothFrameEncode A J α hs ht E a x,smoothFrameEncode A J α hs ht E b x⟫
      ∂geometricVolume A J α) = ⟪a,b⟫ := by
  rw [preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (normalizedFrameEncode_inner A J α ht E hE a.val b.val)

def l2Coefficients : L2 A J α hs ht true →ₗᵢ[ℝ]
    Lp (HilbertFrame A) 2 (geometricVolume A J α) :=
  isometryFromCompletion (lpEncodeIsometry (smoothFrameEncode A J α hs ht E)
    (smoothFrameEncode_memLp A J α hs ht E hE)
    (smoothFrameEncode_inner_integral A J α hs ht E hE))

lemma l2Coefficients_smooth (a : PreL2 A J α hs ht true) :
    ∀ᵐ x ∂geometricVolume A J α,
      l2Coefficients A J α hs ht E hE (smoothL2 A J α hs ht true a) x =
        normalizedFrameEncode A J α ht E x (a.val x) := by
  change ∀ᵐ x ∂geometricVolume A J α,
    isometryFromCompletion (lpEncodeIsometry (smoothFrameEncode A J α hs ht E)
      (smoothFrameEncode_memLp A J α hs ht E hE)
      (smoothFrameEncode_inner_integral A J α hs ht E hE))
        (a : UniformSpace.Completion (PreL2 A J α hs ht true)) x = _
  rw [isometryFromCompletion_coe]
  exact (smoothFrameEncode_memLp A J α hs ht E hE a).coeFn_toLp

lemma l2Coefficients_pairing (Q : L2 A J α hs ht true) (a : PreL2 A J α hs ht true) :
    ⟪Q,smoothL2 A J α hs ht true a⟫ =
      ∫ x, ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (a.val x)⟫ ∂geometricVolume A J α := by
  rw [← (l2Coefficients A J α hs ht E hE).inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Coefficients_smooth A J α hs ht E hE a] with x hx
  rw [hx]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end

end OAI
