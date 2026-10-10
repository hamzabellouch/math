import Mathlib
import OAI.MathematicalPhysics.BFSS.GaugeOrbits

namespace OAI

/-! Exponential normal charts, derivatives, Jacobians and local integration. -/

namespace BFSSSlice
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exp_linear_strictFDeriv_zero (L : E →L[ℝ] A) :
    HasStrictFDerivAt (fun z => NormedSpace.exp (L z)) L 0 := by
  have h0 : HasStrictFDerivAt NormedSpace.exp (1 : A →L[ℝ] A) (L 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
  have he := h0.comp 0 L.hasStrictFDerivAt
  convert! he using 1

def conjugationDifferential (W X : E →L[ℝ] A) (a : A) :
    E →L[ℝ] A :=
  (ContinuousLinearMap.mulLeftRight ℝ A 1 a).comp W + X -
    (ContinuousLinearMap.mulLeftRight ℝ A a 1).comp W

omit [CompleteSpace A] in
lemma conjugationDifferential_apply (W X : E →L[ℝ] A) (a : A) (z : E) :
    conjugationDifferential W X a z = W z * a + X z - a * W z := by
  simp [conjugationDifferential]

lemma exp_conj_strictFDeriv_zero (W X : E →L[ℝ] A) (a : A) :
    HasStrictFDerivAt (fun z => NormedSpace.exp (W z)*(a+X z)*NormedSpace.exp (-W z))
      (conjugationDifferential W X a) 0 := by
  have hw := exp_linear_strictFDeriv_zero W
  have hx := (hasStrictFDerivAt_const a (0:E)).add X.hasStrictFDerivAt
  have hn := exp_linear_strictFDeriv_zero (-W)
  have hd := (hw.mul' hx).mul' hn
  convert! hd using 1
  ext z
  simp [conjugationDifferential_apply,NormedSpace.exp_zero,sub_eq_add_neg]
  abel

end
end BFSSSlice
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

def gaugeTangentLift (q : Boson N) : LinearMap.range (M.gaugeTangent q) →ₗ[ℝ] ColorVector N :=
  Classical.choose ((M.gaugeTangent q).rangeRestrict.exists_rightInverse_of_surjective
    (M.gaugeTangent q).range_rangeRestrict)

lemma gaugeTangentLift_right (q : Boson N) (v : LinearMap.range (M.gaugeTangent q)) :
    M.gaugeTangent q (M.gaugeTangentLift q v) = v := by
  have he := Classical.choose_spec ((M.gaugeTangent q).rangeRestrict.exists_rightInverse_of_surjective
    (M.gaugeTangent q).range_rangeRestrict)
  exact congrArg Subtype.val (LinearMap.congr_fun he v)

abbrev SliceParameter (M : AlgebraData N) (q : Boson N) :=
  LinearMap.range (M.gaugeTangent q) × M.normalSlice q

def sliceLinearEquiv (q : Boson N) : M.SliceParameter q ≃L[ℝ] Boson N :=
  ((LinearMap.range (M.gaugeTangent q)).prodEquivOfIsCompl (M.normalSlice q)
    (LinearMap.range (M.gaugeTangent q)).isCompl_orthogonal).toContinuousLinearEquiv

lemma sliceLinearEquiv_apply (q : Boson N) (v : M.SliceParameter q) :
    M.sliceLinearEquiv q v = (v.1 : Boson N)+(v.2 : Boson N) := rfl

def sliceGaugeLift (q : Boson N) : M.SliceParameter q →L[ℝ] ColorVector N :=
  (M.gaugeTangentLift q).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)

def sliceNormalTranslation (q : Boson N) : M.SliceParameter q →L[ℝ] Boson N :=
  (M.normalSlice q).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

def sliceGaugeGenerator (q : Boson N) : M.SliceParameter q →L[ℝ] ColorMatrix N :=
  ((-Complex.I) • M.colorEmbed.toContinuousLinearMap).comp (M.sliceGaugeLift q)

lemma sliceGaugeGenerator_apply (q : Boson N) (v : M.SliceParameter q) :
    M.sliceGaugeGenerator q v = (-Complex.I) • M.colorEmbed (M.gaugeTangentLift q v.1) := rfl

def normalChartMap (q : Boson N) (v : M.SliceParameter q) : Boson N :=
  M.gaugeConjugate (NormedSpace.exp (M.sliceGaugeGenerator q v)) (q+M.sliceNormalTranslation q v)

lemma normalChartMap_zero (q : Boson N) : M.normalChartMap q 0 = q := by
  simp only [normalChartMap,map_zero,NormedSpace.exp_zero,add_zero,M.gaugeConjugate_one]

lemma gaugeExponential_star (w : ColorVector N) :
    (NormedSpace.exp ((-Complex.I) • M.colorEmbed w))ᴴ =
      NormedSpace.exp (-((-Complex.I) • M.colorEmbed w)) := by
  simpa only [one_smul] using
    BFSSGaugeFlow.exp_conj_reverse (M.colorEmbed w) (M.colorCombination_hermitian w) 1

lemma gaugeExponential_unitary (w : ColorVector N) :
    NormedSpace.exp ((-Complex.I) • M.colorEmbed w) ∈ unitary (ColorMatrix N) := by
  simpa only [one_smul] using
    BFSSGaugeFlow.exp_skew (M.colorEmbed w) (M.colorCombination_hermitian w) 1

def sliceSpatialTranslation (q : Boson N) (i : SpaceIndex) :
    M.SliceParameter q →L[ℝ] ColorMatrix N :=
  M.colorEmbed.toContinuousLinearMap.comp
    ((spatialColorMap (N := N) i).toContinuousLinearMap.comp (M.sliceNormalTranslation q))

lemma normalChartMap_spatial (q : Boson N) (v : M.SliceParameter q) (i : SpaceIndex) :
    spatialColor (M.normalChartMap q v) i =
      M.colorExtract (NormedSpace.exp (M.sliceGaugeGenerator q v) *
        (M.colorEmbed (spatialColor q i)+M.sliceSpatialTranslation q i v) *
          NormedSpace.exp (-(M.sliceGaugeGenerator q v))) := by
  change M.colorExtract (NormedSpace.exp (M.sliceGaugeGenerator q v) *
      M.colorEmbed (spatialColor (q+M.sliceNormalTranslation q v) i) *
        (NormedSpace.exp (M.sliceGaugeGenerator q v))ᴴ) = _
  rw [sliceGaugeGenerator_apply,M.gaugeExponential_star]
  rw [show spatialColor (q+M.sliceNormalTranslation q v) i =
    spatialColor q i+spatialColor (M.sliceNormalTranslation q v) i from rfl, map_add]
  rfl

lemma slice_spatial_differential (q : Boson N) (i : SpaceIndex) :
    M.colorExtract.toContinuousLinearMap.comp
      (BFSSSlice.conjugationDifferential (M.sliceGaugeGenerator q)
        (M.sliceSpatialTranslation q i) (M.colorEmbed (spatialColor q i))) =
      (spatialColorMap (N := N) i).toContinuousLinearMap.comp (M.sliceLinearEquiv q : _ →L[ℝ] _) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply,BFSSSlice.conjugationDifferential_apply,
    LinearMap.coe_toContinuousLinearMap',M.sliceGaugeGenerator_apply]
  have he :
      ((-Complex.I) • M.colorEmbed (M.gaugeTangentLift q v.1))*M.colorEmbed (spatialColor q i) +
          M.sliceSpatialTranslation q i v -
            M.colorEmbed (spatialColor q i)*((-Complex.I) • M.colorEmbed (M.gaugeTangentLift q v.1)) =
      AlgebraData.bracket (M.colorEmbed (M.gaugeTangentLift q v.1)) (M.colorEmbed (spatialColor q i))+
        M.colorEmbed (spatialColor (v.2 : Boson N) i) := by
    change _ + M.colorEmbed (spatialColor (v.2 : Boson N) i) - _ = _
    simp only [AlgebraData.bracket,smul_sub,smul_mul_assoc,mul_smul_comm]
    abel
  rw [he,map_add,M.colorExtract_bracket,M.colorExtract_embed]
  have ht := congrArg (fun x => spatialColor x i) (M.gaugeTangentLift_right q v.1)
  rw [M.spatialColor_gaugeTangent] at ht
  rw [ht]
  rfl

lemma normalChart_spatial_strictFDeriv (q : Boson N) (i : SpaceIndex) :
    HasStrictFDerivAt (fun v => spatialColor (M.normalChartMap q v) i)
      ((spatialColorMap (N := N) i).toContinuousLinearMap.comp (M.sliceLinearEquiv q : _ →L[ℝ] _)) 0 := by
  have hd0 := BFSSSlice.exp_conj_strictFDeriv_zero (M.sliceGaugeGenerator q)
      (M.sliceSpatialTranslation q i) (M.colorEmbed (spatialColor q i))
  have hd := (M.colorExtract.toContinuousLinearMap.hasStrictFDerivAt).comp 0
    hd0
  rw [M.slice_spatial_differential] at hd
  have heq : (fun v => M.colorExtract
      (NormedSpace.exp (M.sliceGaugeGenerator q v) *
        (M.colorEmbed (spatialColor q i)+M.sliceSpatialTranslation q i v) *
          NormedSpace.exp (-(M.sliceGaugeGenerator q v)))) =
      (fun v => spatialColor (M.normalChartMap q v) i) := by
    funext v
    exact (M.normalChartMap_spatial q v i).symm
  change HasStrictFDerivAt (fun v => M.colorExtract
      (NormedSpace.exp (M.sliceGaugeGenerator q v) *
        (M.colorEmbed (spatialColor q i)+M.sliceSpatialTranslation q i v) *
          NormedSpace.exp (-(M.sliceGaugeGenerator q v)))) _ 0 at hd
  rw [heq] at hd
  exact hd
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma normalChartMap_strictFDeriv (q : Boson N) :
    HasStrictFDerivAt (M.normalChartMap q) (M.sliceLinearEquiv q : _ →L[ℝ] _) 0 := by
  have hd : HasStrictFDerivAt (fun v : M.SliceParameter q =>
      fun i : SpaceIndex => spatialColor (M.normalChartMap q v) i)
      (ContinuousLinearMap.pi fun i =>
        (spatialColorMap (N := N) i).toContinuousLinearMap.comp
          (M.sliceLinearEquiv q : _ →L[ℝ] _)) 0 :=
    hasStrictFDerivAt_pi.mpr (M.normalChart_spatial_strictFDeriv q)
  have he := ((bosonAssemble (N := N)).toContinuousLinearMap.hasStrictFDerivAt).comp 0 hd
  convert! he using 1

def normalLocalChart (q : Boson N) : OpenPartialHomeomorph (M.SliceParameter q) (Boson N) :=
  (M.normalChartMap_strictFDeriv q).toOpenPartialHomeomorph (M.normalChartMap q)

lemma normalLocalChart_coe (q : Boson N) :
    (M.normalLocalChart q : M.SliceParameter q → Boson N) = M.normalChartMap q := rfl

lemma normalLocalChart_source (q : Boson N) : 0 ∈ (M.normalLocalChart q).source :=
  (M.normalChartMap_strictFDeriv q).mem_toOpenPartialHomeomorph_source

lemma normalLocalChart_target (q : Boson N) : q ∈ (M.normalLocalChart q).target := by
  change q ∈ ((M.normalChartMap_strictFDeriv q).toOpenPartialHomeomorph (M.normalChartMap q)).target
  simpa only [M.normalChartMap_zero] using
    (M.normalChartMap_strictFDeriv q).image_mem_toOpenPartialHomeomorph_target

lemma normalLocalChart_inverse (q : Boson N) : (M.normalLocalChart q).symm q = 0 := by
  simpa only [M.normalLocalChart_coe,M.normalChartMap_zero] using
    (M.normalLocalChart q).left_inv (M.normalLocalChart_source q)

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma normalChartMap_contDiff (q : Boson N) :
    ContDiff ℝ (⊤ : ℕ∞) (M.normalChartMap q) := by
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : ColorMatrix N → ColorMatrix N) := by
    exact contDiff_iff_contDiffAt.mpr (fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt)
  have hcoord (i : SpaceIndex) :
      ContDiff ℝ (⊤ : ℕ∞) (fun v : M.SliceParameter q => spatialColor (M.normalChartMap q v) i) := by
    have he := M.colorExtract.toContinuousLinearMap.contDiff.comp
      (((hexp.comp (M.sliceGaugeGenerator q).contDiff).mul
        ((contDiff_const (c := M.colorEmbed (spatialColor q i))).add
          (M.sliceSpatialTranslation q i).contDiff)).mul
        (hexp.comp (M.sliceGaugeGenerator q).contDiff.neg))
    have heq : (fun v : M.SliceParameter q => spatialColor (M.normalChartMap q v) i) =
        (fun v => M.colorExtract (NormedSpace.exp (M.sliceGaugeGenerator q v) *
          (M.colorEmbed (spatialColor q i)+M.sliceSpatialTranslation q i v) *
            NormedSpace.exp (-(M.sliceGaugeGenerator q v)))) :=
      funext (fun v => M.normalChartMap_spatial q v i)
    rw [heq]
    exact he
  have ha := (bosonAssemble (N := N)).toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mpr hcoord)
  convert! ha using 1

def normalEuclideanChart (q : Boson N) (x : Boson N) : Boson N :=
  M.normalChartMap q ((M.sliceLinearEquiv q).symm x)

lemma normalEuclideanChart_contDiff (q : Boson N) :
    ContDiff ℝ (⊤ : ℕ∞) (M.normalEuclideanChart q) :=
  (M.normalChartMap_contDiff q).comp (M.sliceLinearEquiv q).symm.contDiff

lemma normalEuclideanChart_zero (q : Boson N) : M.normalEuclideanChart q 0 = q := by
  simp only [normalEuclideanChart,map_zero,M.normalChartMap_zero]

lemma normalEuclideanChart_strictFDeriv_zero (q : Boson N) :
    HasStrictFDerivAt (M.normalEuclideanChart q) (ContinuousLinearMap.id ℝ (Boson N)) 0 := by
  have ho : HasStrictFDerivAt (M.normalChartMap q)
      (M.sliceLinearEquiv q : M.SliceParameter q →L[ℝ] Boson N)
      ((M.sliceLinearEquiv q).symm (0 : Boson N)) := by
    simpa only [map_zero] using M.normalChartMap_strictFDeriv q
  have hd := ho.comp (0 : Boson N)
    (M.sliceLinearEquiv q).symm.toContinuousLinearMap.hasStrictFDerivAt
  convert! hd using 1
  ext x
  simp

def normalChartJacobian (q x : Boson N) : ℝ :=
  (fderiv ℝ (M.normalEuclideanChart q) x).det

lemma normalChartJacobian_continuous (q : Boson N) :
    Continuous (M.normalChartJacobian q) :=
  ContinuousLinearMap.continuous_det.comp
    ((M.normalEuclideanChart_contDiff q).continuous_fderiv (by simp))

lemma normalChartJacobian_zero (q : Boson N) : M.normalChartJacobian q 0 = 1 := by
  rw [normalChartJacobian,(M.normalEuclideanChart_strictFDeriv_zero q).hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.det]

theorem normalChart_local_integral (q : Boson N) :
    ∃ U : Set (Boson N), IsOpen U ∧ 0 ∈ U ∧
      Set.InjOn (M.normalEuclideanChart q) U ∧
      (∀ x ∈ U, 1/2 < M.normalChartJacobian q x ∧ M.normalChartJacobian q x < 2) ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F], ∀ g : Boson N → F,
      (∫ x in M.normalEuclideanChart q '' U, g x) =
        ∫ x in U, M.normalChartJacobian q x • g (M.normalEuclideanChart q x) := by
  let e := (M.normalEuclideanChart_strictFDeriv_zero q).toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ (Boson N)) (M.normalEuclideanChart q)
  let V := (M.normalChartJacobian q) ⁻¹' Set.Ioo (1/2) 2
  have hV : IsOpen V := isOpen_Ioo.preimage (M.normalChartJacobian_continuous q)
  have h0V : (0 : Boson N) ∈ V := by
    change 1/2 < M.normalChartJacobian q 0 ∧ M.normalChartJacobian q 0 < 2
    rw [M.normalChartJacobian_zero]
    norm_num
  have h0e : (0 : Boson N) ∈ e.source :=
    (M.normalEuclideanChart_strictFDeriv_zero q).mem_toOpenPartialHomeomorph_source
      (f' := ContinuousLinearEquiv.refl ℝ (Boson N))
  refine ⟨e.source ∩ V,e.open_source.inter hV,⟨h0e,h0V⟩,
    e.injOn.mono Set.inter_subset_left,(fun x hx => hx.2),?_⟩
  intro F _ _ g
  have hi := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure (Boson N)) (e.open_source.inter hV).measurableSet
    (fun x hx => ((M.normalEuclideanChart_contDiff q).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
    (e.injOn.mono Set.inter_subset_left) g
  change (∫ x in M.normalEuclideanChart q '' (e.source ∩ V), g x) = _ at hi
  rw [hi]
  apply setIntegral_congr_fun (e.open_source.inter hV).measurableSet
  intro x hx
  change |M.normalChartJacobian q x| • _ = _
  rw [abs_of_pos (lt_trans (by norm_num) hx.2.1)]

end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma sliceLinearEquiv_measurePreserving (q : Boson N) :
    MeasurePreserving (M.sliceLinearEquiv q) volume volume := by
  let K := LinearMap.range (M.gaugeTangent q)
  have hp := K.orthogonalDecomposition.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp K Kᗮ)
  change MeasurePreserving (fun v : K × Kᗮ =>
    (v.1 : Boson N) + (v.2 : Boson N)) volume volume
  convert hp using 1
  rfl

lemma normalChartMap_invariant (q : Boson N) (F : Boson N → ℝ)
    (hF : ∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x)
    (v : M.SliceParameter q) :
    F (M.normalChartMap q v) = F (q + (v.2 : Boson N)) := by
  exact hF ⟨_,M.gaugeExponential_unitary (M.gaugeTangentLift q v.1)⟩ _

end
end BFSSQuantum.AlgebraData

end OAI
