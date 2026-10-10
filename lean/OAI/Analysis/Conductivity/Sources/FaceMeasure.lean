import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularMeasureExact

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance sourceFaceMeasureCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sourceFaceMeasureCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sourceFaceParameter (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ × UnitAddTorus (Fin 2) :=
  (x 0,torusAngles (sourceFaceAngles i j x))

def sourceFaceWeight (i j : Fin 4) (x : Fin 3 → ℝ) : ℝ :=
  faceRayDensity 1 i (x 1)*faceRayDensity sourceRadialWidth j (x 2)

lemma continuous_sourceFaceParameter (i j : Fin 4) : Continuous (sourceFaceParameter i j) := by
  unfold sourceFaceParameter
  simp_rw [sourceFaceAngles_torus]
  apply (continuous_apply 0).prodMk
  apply continuous_pi
  intro k
  fin_cases k
  · exact (continuous_faceRayCircle 1 i).comp (continuous_apply 1)
  · exact (continuous_faceRayCircle sourceRadialWidth j).comp (continuous_apply 2)

lemma continuous_sourceFaceWeight (i j : Fin 4) : Continuous (sourceFaceWeight i j) :=
  ((continuous_faceRayDensity 1 i).comp (continuous_apply 1)).mul
    ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))

lemma sourceFaceWeight_pos (i j : Fin 4) (x : Fin 3 → ℝ) : 0<sourceFaceWeight i j x :=
  mul_pos (faceRayDensity_pos' (by norm_num) i (x 1))
    (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))

def sourceFaceMeasure (l r : ℝ) (i j : Fin 4) : Measure (ℝ × UnitAddTorus (Fin 2)) :=
  Measure.map (sourceFaceParameter i j) ((volume.restrict (sourceExtendedBox l r)).withDensity
    (fun x => ENNReal.ofReal (sourceFaceWeight i j x)))

instance finite_sourceFaceMeasure (l r : ℝ) (i j : Fin 4) :
    IsFiniteMeasure (sourceFaceMeasure l r i j) := by
  have h : IntegrableOn (sourceFaceWeight i j) (sourceExtendedBox l r) volume :=
    (continuous_sourceFaceWeight i j).continuousOn.integrableOn_compact isCompact_Icc
  have := isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral
  unfold sourceFaceMeasure
  infer_instance

lemma integral_sourceFaceMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l r : ℝ) (i j : Fin 4) {F : ℝ × UnitAddTorus (Fin 2) → E}
    (hF : AEStronglyMeasurable F (sourceFaceMeasure l r i j)) :
    (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ x in sourceExtendedBox l r,sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  rw [sourceFaceMeasure,integral_map (continuous_sourceFaceParameter i j).aemeasurable hF,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (sourceFaceWeight_pos i j x).le]

lemma integral_sourceFaceWeight_continuous {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) {l r : ℝ} (hlr : l≤r) :
    (∫ x in sourceExtendedBox l r,sourceFaceWeight i j x * F (sourceFaceParameter i j x))=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
  rw [integral_sourceExtendedBox (g:=fun x => sourceFaceWeight i j x * F (sourceFaceParameter i j x)) ((continuous_sourceFaceWeight i j).mul
    (hF.comp (continuous_sourceFaceParameter i j))) hlr]
  congr 1
  funext t
  congr 1
  funext a
  rw [←intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro b _
  simp only [sourceFaceWeight,sourceFaceParameter,sourceFaceAngles_torus,torusFaceTerm,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  ring

lemma continuous_sourceFaceIntegral {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) :
    Continuous (fun t => ∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a) := by
  apply continuous_parametric_unitInterval
  apply Continuous.mul
  · apply continuous_parametric_unitInterval
    unfold torusFaceTerm
    apply Continuous.mul
    · apply hF.comp
      apply continuous_fst.fst.prodMk
      apply continuous_pi
      intro k
      fin_cases k
      · exact (continuous_faceRayCircle 1 i).comp continuous_fst.snd
      · exact (continuous_faceRayCircle sourceRadialWidth j).comp continuous_snd
    · exact (continuous_faceRayDensity sourceRadialWidth j).comp continuous_snd
  · exact (continuous_faceRayDensity 1 i).comp continuous_snd

theorem sourceCylinderMeasure_eq_faces {l r : ℝ} (hlr : l≤r) :
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))=
      ∑ i : Fin 4,∑ j : Fin 4,sourceFaceMeasure l r i j := by
  have : ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  have hi : Integrable (fun z => F z)
      ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))) := F.integrable
  rw [integral_prod _ hi,←intervalIntegral.integral_of_le hlr]
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => F.integrable))]
  simp_rw [integral_finsetSum_measure (fun j _ => F.integrable)]
  have hh (i j : Fin 4) : (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
    rw [integral_sourceFaceMeasure (F:=fun z => F z) l r i j F.continuous.aestronglyMeasurable]
    exact integral_sourceFaceWeight_continuous F.continuous i j hlr
  simp_rw [hh]
  have he (t : ℝ) := integral_unitTorus_faces (w₀:=1) (w₁:=sourceRadialWidth)
    (F:=fun θ => F (t,θ)) (by norm_num) (by norm_num [sourceRadialWidth,sourceHole])
    (F.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun θ => F (t,θ)))
  simp only [volume_pi,unitCircle_volume_eq_haar] at he
  trans ∫ t in l..r,∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a
  · apply intervalIntegral.integral_congr
    intro t _
    exact he t
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j)).intervalIntegrable l r)]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_finsetSum (fun j _ =>
    (continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j).intervalIntegrable l r)

end ScalarConductivity

end
end

end OAI
