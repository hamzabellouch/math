import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildCentralL2

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

lemma sourceChildInverse_map_volume (σ : ℝ) :
    Measure.map (sourceChildHomeomorph σ).symm volume=ENNReal.ofReal (sourceScale^3) • volume := by
  apply (sourceChildHomeomorph σ).toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map (sourceChildHomeomorph σ) (Measure.map (sourceChildHomeomorph σ).symm volume)=
    Measure.map (sourceChildHomeomorph σ) (ENNReal.ofReal (sourceScale^3) • volume)
  rw [Measure.map_map (sourceChildHomeomorph σ).measurable (sourceChildHomeomorph σ).symm.measurable]
  have he : (sourceChildHomeomorph σ) ∘ (sourceChildHomeomorph σ).symm=id :=
    funext (sourceChildHomeomorph σ).apply_symm_apply
  rw [he,Measure.map_id,Measure.map_smul _ (sourceChildHomeomorph σ).measurable.aemeasurable]
  change volume=ENNReal.ofReal (sourceScale^3) • Measure.map (sourceChildCoordinates σ) volume
  rw [sourceChildCoordinates_map_volume,smul_smul,←ENNReal.ofReal_mul (by norm_num [sourceScale])]
  norm_num [sourceScale]

lemma sourceChildInverse_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildHomeomorph σ).symm volume volume := by
  refine ⟨(sourceChildHomeomorph σ).symm.measurable,?_⟩
  rw [sourceChildInverse_map_volume]
  exact Measure.smul_absolutelyContinuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceChildPushforwardCLM (σ : ℝ) : Lp E 2 (volume : Measure (Fin 3 → ℝ)) →L[ℝ]
    Lp E 2 (volume : Measure (Fin 3 → ℝ)) :=
  lpBoundedPullbackCLM (sourceChildHomeomorph σ).symm.toMeasurableEquiv ENNReal.ofReal_ne_top
    (le_of_eq (sourceChildInverse_map_volume σ))

lemma sourceChildPushforwardCLM_ae (σ : ℝ) (f : Lp E 2 (volume : Measure (Fin 3 → ℝ))) :
    sourceChildPushforwardCLM σ f=ᵐ[volume] (fun y => f ((sourceChildHomeomorph σ).symm y)) :=
  lpBoundedPullbackCLM_ae _ _ _ f

lemma sourceChildInverse_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceChildHomeomorph]
  all_goals fun_prop

def sourceChildInverseDerivative : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (sourceScale^2)⁻¹ • sourceChildDerivative

lemma sourceChildInverseDerivative_apply (y : Fin 3 → ℝ) :
    sourceChildInverseDerivative y=![y 1/sourceScale,y 0/sourceScale,y 2/sourceScale] := by
  rw [sourceChildInverseDerivative,smul_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> norm_num [sourceScale] <;> ring

lemma sourceChildInverse_hasFDeriv (σ : ℝ) (y : Fin 3 → ℝ) :
    HasFDerivAt ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) sourceChildInverseDerivative y := by
  have he : ((sourceChildHomeomorph σ).symm : (Fin 3 → ℝ) → (Fin 3 → ℝ))=
      fun y => sourceChildInverseDerivative y+![0,-σ*sourceOffset/sourceScale,0] := by
    funext y
    rw [sourceChildInverseDerivative_apply]
    ext i
    fin_cases i <;> simp [sourceChildHomeomorph]; ring
  rw [he]
  exact sourceChildInverseDerivative.hasFDerivAt.add_const _

lemma sourceChildInverse_single (i : Fin 3) :
    sourceChildInverseDerivative (Pi.single i 1)=sourceScale⁻¹ • Pi.single (childAxis i) 1 := by
  rw [sourceChildInverseDerivative_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> norm_num [childAxis,Pi.single_apply,Fin.ext_iff,sourceScale]

end

open Set MeasureTheory Filter Topology

lemma sourceChild_euclidean_norm (σ : ℝ) (y : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (sourceChildCoordinates σ y)‖ ≤ sourceScale * ‖WithLp.toLp 2 y‖ + |σ*sourceOffset| := by
  let v : R3 := WithLp.toLp 2 ![y 1,y 0,y 2]
  have hv : ‖v‖=‖WithLp.toLp 2 y‖ := by
    have h₀ := EuclideanSpace.real_norm_sq_eq v
    have h₁ := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : R3)
    simp [v,Fin.sum_univ_succ] at h₀ h₁
    nlinarith [norm_nonneg v,norm_nonneg (WithLp.toLp 2 y : R3)]
  have he : (WithLp.toLp 2 (sourceChildCoordinates σ y) : R3)=
      sourceScale • v+EuclideanSpace.single 0 (σ*sourceOffset) := by
    ext i
    fin_cases i <;> simp [sourceChildCoordinates,v]
  rw [he]
  calc
    _ ≤ ‖sourceScale • v‖+‖EuclideanSpace.single 0 (σ*sourceOffset)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,hv,PiLp.norm_single,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ sourceScale by norm_num [sourceScale])]

def sourceChildEuclidean (σ : ℝ) : R3 ≃ₜ R3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.trans
    ((sourceChildHomeomorph σ).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph)

lemma sourceChildEuclidean_apply (σ : ℝ) (x : R3) :
    sourceChildEuclidean σ x=WithLp.toLp 2 (sourceChildCoordinates σ (WithLp.ofLp x)) := rfl

lemma sourceChildEuclidean_symm_apply (σ : ℝ) (x : R3) :
    (sourceChildEuclidean σ).symm x=WithLp.toLp 2 ((sourceChildHomeomorph σ).symm (WithLp.ofLp x)) := rfl

lemma sourceChildEuclidean_symm_contDiff (σ : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) ((sourceChildEuclidean σ).symm : R3 → R3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    ((sourceChildInverse_contDiff σ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)

lemma sourceChildEuclidean_ball (k : Fin 2) : sourceChildEuclidean (actualChildSign k) '' ball⊆ball := by
  rintro x ⟨y,hy,rfl⟩
  have hn := sourceChild_euclidean_norm (actualChildSign k) (WithLp.ofLp y)
  have hσ : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  rw [abs_mul,hσ,one_mul] at hn
  change ‖WithLp.toLp 2 (sourceChildCoordinates (actualChildSign k) (WithLp.ofLp y))‖ ≤ sourceScale * ‖y‖ + |sourceOffset| at hn
  change dist (sourceChildEuclidean (actualChildSign k) y) 0<3
  rw [dist_zero_right,sourceChildEuclidean_apply]
  have hy' : ‖y‖<3 := by simpa only [ball,Metric.mem_ball,dist_zero_right] using hy
  norm_num [sourceScale,sourceOffset] at hn
  linarith

lemma sourceChildEuclidean_comp_support (k : Fin 2) {f : R3 → ℝ}
    (hs : tsupport f⊆ball) :
    tsupport (f ∘ (sourceChildEuclidean (actualChildSign k)).symm)⊆ball := by
  intro x hx
  have hy := tsupport_comp_subset_preimage f (sourceChildEuclidean (actualChildSign k)).symm.continuous hx
  have him : x∈sourceChildEuclidean (actualChildSign k) '' ball :=
    ⟨(sourceChildEuclidean (actualChildSign k)).symm x,hs hy,(sourceChildEuclidean (actualChildSign k)).apply_symm_apply x⟩
  exact sourceChildEuclidean_ball k him

end ScalarConductivity

end

end OAI
