import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularIntegration

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma unitCircle_volume_eq_haar : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1))

lemma integral_unitTorus_iterated {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    (∫ x,F x)=∫ θ : UnitAddCircle,∫ φ : UnitAddCircle,F ![θ,φ]
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have hc : Continuous (MeasurableEquiv.finTwoArrow.symm :
      UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) := by
    change Continuous (fun p : UnitAddCircle × UnitAddCircle => ![p.1,p.2])
    fun_prop
  rw [←(volume_preserving_finTwoArrow UnitAddCircle).symm.integral_comp']
  change (∫ x : UnitAddCircle × UnitAddCircle,F (MeasurableEquiv.finTwoArrow.symm x)
    ∂volume.prod volume)=_
  rw [integral_prod (fun x : UnitAddCircle × UnitAddCircle => F (MeasurableEquiv.finTwoArrow.symm x))
    ((hF.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [unitCircle_volume_eq_haar]
  rfl

lemma continuous_faceRayAngle (w : ℝ) (j : Fin 4) : Continuous (faceRayAngle w j) :=
  continuous_iff_continuousAt.mpr (fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

lemma continuous_parametric_unitInterval {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun x => ∫ b in (-1:ℝ)..1,f x b) := by
  have hh := continuous_parametric_integral_of_continuous (μ:=volume) hf (s:=Icc (-1:ℝ) 1) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),
    integral_Icc_eq_integral_Ioc] using hh

lemma continuous_torus_partial_integral {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    Continuous (fun θ : UnitAddCircle => ∫ φ : UnitAddCircle,F ![θ,φ]
      ∂AddCircle.haarAddCircle) := by
  have hh := continuous_parametric_integral_of_continuous
    (μ:=AddCircle.haarAddCircle) (f:=fun θ φ : UnitAddCircle => F ![θ,φ])
    (hF.comp (by change Continuous (fun p : UnitAddCircle × UnitAddCircle => ![p.1,p.2]); fun_prop))
    (s:=univ) isCompact_univ
  simpa using hh

def torusFaceTerm (w₀ w₁ : ℝ) (F : UnitAddTorus (Fin 2) → ℝ)
    (j k : Fin 4) (a b : ℝ) : ℝ :=
  F ![((faceRayAngle w₀ j a:ℝ):UnitAddCircle),((faceRayAngle w₁ k b:ℝ):UnitAddCircle)]*
    faceRayDensity w₁ k b

lemma continuous_torusFaceTerm (w₀ w₁ : ℝ) {F : UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (j k : Fin 4) :
    Continuous (Function.uncurry (torusFaceTerm w₀ w₁ F j k)) := by
  have h0 := (AddCircle.continuous_mk' 1).comp (continuous_faceRayAngle w₀ j)
  have h1 := (AddCircle.continuous_mk' 1).comp (continuous_faceRayAngle w₁ k)
  have hv : Continuous (fun p : ℝ×ℝ =>
      ![((faceRayAngle w₀ j p.1:ℝ):UnitAddCircle),((faceRayAngle w₁ k p.2:ℝ):UnitAddCircle)]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact h0.comp continuous_fst
    · exact h1.comp continuous_snd
  exact (hF.comp hv).mul ((continuous_faceRayDensity w₁ k).comp continuous_snd)

theorem integral_unitTorus_faces {w₀ w₁ : ℝ} (hw₀ : 0<w₀) (hw₁ : 0<w₁)
    {F : UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F) :
    (∫ x,F x)=∑ j : Fin 4,∑ k : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm w₀ w₁ F j k a b)*faceRayDensity w₀ j a := by
  rw [integral_unitTorus_iterated hF,integral_circle_faces hw₀ (continuous_torus_partial_integral hF)]
  apply Finset.sum_congr rfl
  intro j _
  have hi (a : ℝ) := integral_circle_faces (w:=w₁) hw₁
    (F:=fun φ : UnitAddCircle => F ![((faceRayAngle w₀ j a:ℝ):UnitAddCircle),φ])
    (hF.comp (by fun_prop))
  simp_rw [hi,Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum (fun k _ =>
    ((continuous_parametric_unitInterval (continuous_torusFaceTerm w₀ w₁ hF j k)).mul
      (continuous_faceRayDensity w₀ j)).intervalIntegrable _ _)

lemma sourceAngular_face (t a b : ℝ) (i j : Fin 4) (ha : |a|≤1) (hb : |b|≤1) :
    sourceAngularCollar t
      ![((faceRayAngle 1 i a:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j b:ℝ):UnitAddCircle)]=
      sourceCollarPiece i j ![t,a,b] := by
  have h0 := faceRayAngle_image (w:=1) (by norm_num) i ha
  have h1 := faceRayAngle_image (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) j hb
  ext k
  fin_cases k <;>
    simp [sourceAngularCollar,sourceAngularPolynomial,sourceRayCoordinates,h0,h1,
      sourceCollarPiece,sourceCollarRadius] <;> ring_nf <;> simp

lemma sourceAngularFace_continuous (t : ℝ) (i j : Fin 4) :
    Continuous (fun p : ℝ×ℝ => sourceCollarPiece i j ![t,p.1,p.2]) := by
  exact (sourceCollarPiece_contDiff i j).continuous.comp (by fun_prop)

theorem integral_sourceAngular_le {f : (Fin 3 → ℝ) → ℝ}
    (hf : Continuous f) (hn : ∀ z,0≤f z) (t : ℝ) :
    (∫ x : UnitAddTorus (Fin 2),f (sourceAngularCollar t x))≤
      ((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))*
        ∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,
          f (sourceCollarPiece i j ![t,a,b]) := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hw' : sourceRadialWidth≤1 := by norm_num [sourceRadialWidth,sourceHole]
  let c₀ : ℝ := 1/(2*Real.pi)
  let c₁ : ℝ := (1/sourceRadialWidth)/(2*Real.pi)
  have hc₀ : 0≤c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0≤c₁ := by dsimp [c₁]; positivity
  change _≤ c₁*c₀*_
  rw [integral_unitTorus_faces (F:=fun x => f (sourceAngularCollar t x)) (w₀:=1) (w₁:=sourceRadialWidth) (by norm_num) hw
    (hf.comp (continuous_sourceAngularCollar t))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((continuous_parametric_unitInterval
      (continuous_torusFaceTerm 1 sourceRadialWidth (hf.comp (continuous_sourceAngularCollar t)) i j)).mul
        (continuous_faceRayDensity 1 i)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_parametric_unitInterval (f:=fun a b => f (sourceCollarPiece i j ![t,a,b]))
      (hf.comp (sourceAngularFace_continuous t i j)))).intervalIntegrable _ _
  · intro a ha
    have hinner : (∫ b in (-1:ℝ)..1,
        torusFaceTerm 1 sourceRadialWidth (fun x => f (sourceAngularCollar t x)) i j a b)≤
        c₁*(∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact ((continuous_torusFaceTerm 1 sourceRadialWidth
          (hf.comp (continuous_sourceAngularCollar t)) i j).comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · exact (continuous_const.mul ((hf.comp (sourceAngularFace_continuous t i j)).comp
          (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
      · intro b hb
        dsimp only [torusFaceTerm]
        rw [sourceAngular_face t a b i j (abs_le.mpr ha) (abs_le.mpr hb)]
        exact (mul_le_mul_of_nonneg_left (faceRayDensity_bounds hw hw' j b).2 (hn _)).trans_eq
          (mul_comm _ _)
    have hnint : 0≤ ∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b]) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => hn _)
    have hden := faceRayDensity_bounds (w:=1) (by norm_num) (by norm_num) i a
    have hden' : faceRayDensity 1 i a≤c₀ := by simpa [c₀] using hden.2
    calc
      _≤(c₁*(∫ b in (-1:ℝ)..1,f (sourceCollarPiece i j ![t,a,b])))*c₀ :=
        mul_le_mul hinner hden' hden.1 (mul_nonneg hc₁ hnint)
      _=_ := by ring

end ScalarConductivity

end

end OAI
