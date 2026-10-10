import Mathlib
import OAI.Analysis.Conductivity.Flux.AntisymmetricFlux
import OAI.Analysis.Conductivity.Flux.PhysicalEndDifferential
import OAI.Analysis.Conductivity.Variational.PhysicalEndLocalLipschitz
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix

lemma AngularPeriodic.eq_of_angles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) {x y : Coord3}
    (ht : x 0=y 0) (ha : torusAngles x=torusAngles y) : f x=f y := by
  have he (i : Fin 2) : ∃ n : ℤ, x i.succ=y i.succ+(2*Real.pi)*(n:ℝ) := by
    have hi := congrFun ha i
    have heq : ((x i.succ/(2*Real.pi):ℝ) : UnitAddCircle)=
        ((y i.succ/(2*Real.pi):ℝ) : UnitAddCircle) := by
      fin_cases i <;> exact hi
    have hz : (((x i.succ/(2*Real.pi)-y i.succ/(2*Real.pi)):ℝ) : UnitAddCircle)=0 := by
      simpa only [AddCircle.coe_sub,sub_eq_zero] using heq
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
    refine ⟨n,?_⟩
    simp only [zsmul_eq_mul,mul_one] at hn
    have hπ : 2*Real.pi≠0 := by positivity
    field_simp at hn
    nlinarith
  choose n hn using he
  have hxy : x=y+angularShift (2*Real.pi) n := by
    ext i
    fin_cases i
    · simpa [angularShift] using ht
    · simpa [angularShift] using hn 0
    · simpa [angularShift] using hn 1
  rw [hxy]
  exact hp n y

def sourceRealFlat (y : Coord3) : Coord3 :=
  ![sourceCollarTime y,(sourceComplexDirections y 0).arg,
    (sourceComplexDirections y 1).arg]

lemma sourceRealFlat_angles (y : Coord3) :
    torusAngles (sourceRealFlat y)=sourcePhysicalAngles y := by
  ext i
  fin_cases i <;> rfl

def physicalPeriodicField {E : Type*} (f : Coord3 → E) (y : Coord3) : E :=
  f (sourceRealFlat y)

lemma physicalPeriodicField_local_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) {x y : Coord3}
    (hx : ∀ i,sourceComplexDirections x i≠0) (hy : ∀ i,sourceComplexDirections y i≠0) :
    physicalPeriodicField f y=f (sourceLocalFlat x y) := by
  unfold physicalPeriodicField
  apply hp.eq_of_angles (show sourceRealFlat y 0=sourceLocalFlat x y 0 from rfl)
  exact (sourceRealFlat_angles y).trans (sourceLocalFlat_angles hx hy).symm

theorem physicalPeriodicField_localLip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {x : Coord3} (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (physicalPeriodicField f) x := by
  apply ((localLipAt_of_contDiffAt hf.contDiffAt).comp
    (sourceLocalFlat_localLip hx)).congr
  have hd : ∀ᶠ y in 𝓝 x,∀ i,sourceComplexDirections y i≠0 := by
    rw [eventually_all]
    intro i
    exact (locallyLipschitz_sourceDirection i).continuous.continuousAt
      (isOpen_ne.mem_nhds (hx i))
  filter_upwards [hd] with y hy
  exact (physicalPeriodicField_local_eq hp hx hy).symm

lemma measurable_sourceRealFlat : Measurable sourceRealFlat := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact locallyLipschitz_sourceCollarTime.continuous.measurable
  · exact Complex.measurable_arg.comp
      ((continuous_apply 0).comp continuous_sourceComplexDirections).measurable
  · exact Complex.measurable_arg.comp
      ((continuous_apply 1).comp continuous_sourceComplexDirections).measurable

lemma measurable_physicalPeriodicField {E : Type*} [MeasurableSpace E]
    {f : Coord3 → E} (hf : Measurable f) : Measurable (physicalPeriodicField f) :=
  hf.comp measurable_sourceRealFlat

lemma physicalPeriodicField_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    physicalPeriodicField f (sourceCollarPiece i j x)=f (sourceFaceAngles i j x) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  rw [←sourceFaceAngles_physical i j ha hb]
  apply hp.eq_of_angles
  · exact sourceAngular_time ht _
  · rw [sourceRealFlat_angles]
    exact congrArg Prod.snd (sourcePhysicalCoordinates_angular ht _)

lemma physicalPeriodicField_piece_local_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) :
    physicalPeriodicField f =ᶠ[𝓝 (sourceCollarPiece i j x)]
      (fun y => f (sourceFaceAngles i j (sourceCollarInverse i j y))) := by
  change ∀ᶠ y in 𝓝 (sourceCollarPiece i j x),physicalPeriodicField f y=
    f (sourceFaceAngles i j (sourceCollarInverse i j y))
  rw [←sourceCollarPiece_map_nhds i j hx,Filter.eventually_map]
  filter_upwards [isOpen_sourceCollarOpenBox.mem_nhds hx,
    sourceCollarInverse_eventually_left i j hx] with y hy hi
  rw [hi]
  exact physicalPeriodicField_piece hp i j (sourceCollarOpenBox_subset hy)

theorem physicalPeriodicField_hasFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord3 → E} (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    HasFDerivAt (physicalPeriodicField f)
      ((fderiv ℝ f (sourceFaceAngles i j x)).comp
        (((Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap).comp
          (sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)).symm.toContinuousLinearMap))
      (sourceCollarPiece i j x) := by
  have h1 := (sourceCollarInverse_hasStrictFDeriv i j hx).hasFDerivAt
  have he := sourceCollarInverse_point i j hx
  have h2 : HasFDerivAt (sourceFaceAngles i j)
      (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap
      (sourceCollarInverse i j (sourceCollarPiece i j x)) := by
    simpa only [he] using sourceFaceAngles_hasFDeriv i j x
  have h3 : HasFDerivAt f (fderiv ℝ f (sourceFaceAngles i j x))
      (sourceFaceAngles i j (sourceCollarInverse i j (sourceCollarPiece i j x))) := by
    simpa only [he] using (hf (sourceFaceAngles i j x)).hasFDerivAt
  have hh := h2.comp (sourceCollarPiece i j x) h1
  exact (h3.comp (sourceCollarPiece i j x) hh).congr_of_eventuallyEq
    (physicalPeriodicField_piece_local_eq hp i j hx)

theorem physicalPeriodicField_fderiv {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : Differentiable ℝ f)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (v : Coord3) :
    fderiv ℝ (physicalPeriodicField f) (sourceCollarPiece i j x) v =
      (sourceCartesianGradientMatrix i j x *ᵥ
        (fun k => direction (Pi.single k 1) f (sourceFaceAngles i j x))) ⬝ᵥ v := by
  let T := sourceCollarTangentEquiv i j x (sourceCollarOpenBox_subset hx)
  let r : Coord3 := fun k => direction (Pi.single k 1) f (sourceFaceAngles i j x)
  let w := T.symm v
  have hw : sourceCollarJacobian i j x *ᵥ w=v := T.apply_symm_apply v
  have hd : (sourceFaceAngleMatrix i j x)ᵀ=sourceFaceAngleMatrix i j x :=
    Matrix.diagonal_transpose _
  calc
    _ = fderiv ℝ f (sourceFaceAngles i j x) (sourceFaceAngleMatrix i j x *ᵥ w) :=
      congrArg (fun L : Coord3 →L[ℝ] ℝ => L v) (physicalPeriodicField_hasFDeriv hp hf i j hx).fderiv
    _ = r ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ w) := realCLM_apply_basis _ _
    _ = w ⬝ᵥ (sourceFaceAngleMatrix i j x *ᵥ r) := by
      rw [←Matrix.dotProduct_transpose_mulVec,hd]
    _ = w ⬝ᵥ ((sourceCollarJacobian i j x)ᵀ *ᵥ
        (sourceCartesianGradientMatrix i j x *ᵥ r)) := by
      rw [sourceCartesianGradient_chain i j (sourceCollarOpenBox_subset hx)]
    _ = (sourceCartesianGradientMatrix i j x *ᵥ r) ⬝ᵥ
        (sourceCollarJacobian i j x *ᵥ w) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by rw [hw]

end ScalarConductivity

end
end

end OAI
