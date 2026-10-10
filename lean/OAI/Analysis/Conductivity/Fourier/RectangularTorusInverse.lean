import Mathlib
import OAI.Analysis.Conductivity.Fourier.RectangularTorusAtlas

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def sourceCollarInverse (i j : Fin 4) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceCollarTime y,
    squareFaceParameter i ![y 0/sourceLength,y 1]/sourceRadial y,
    squareFaceParameter j (sourceCrossCoordinates y)/(1-sourceCollarTime y)]

lemma sourceCollarPiece_angular (i j : Fin 4) (x : Fin 3 → ℝ) :
    ![sourceCollarPiece i j x 0/sourceLength,sourceCollarPiece i j x 1]=
      sourceCollarRadius j (x 0) (x 2) • squareFace i (x 1) := by
  have hL : sourceLength≠0 := by norm_num [sourceLength]
  ext k; fin_cases k
  · change sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0/sourceLength=_
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
    rfl
  · rfl

lemma sourceCollarInverse_left (i j : Fin 4) {x : Fin 3 → ℝ}
    (ht : x 0∈Ico 0 1) (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
  have ht' : x 0∈Icc 0 1 := ⟨ht.1,ht.2.le⟩
  have hr : sourceCollarRadius j (x 0) (x 2)≠0 := by
    have hh := (sourceCollarRadius_bounds j ht' hb).1
    have hd : 0<sourceHole := by norm_num [sourceHole]
    exact (hd.trans_le hh).ne'
  have hq : 1-x 0≠0 := (sub_pos.mpr ht.2).ne'
  ext k; fin_cases k
  · exact sourceCollarPiece_time i j ht' ha hb
  · change squareFaceParameter i ![sourceCollarPiece i j x 0/sourceLength,
        sourceCollarPiece i j x 1]/sourceRadial (sourceCollarPiece i j x)=x 1
    rw [sourceCollarPiece_angular,squareFace_parameter,sourceCollarPiece_radial i j ht' ha hb]
    exact mul_div_cancel_left₀ _ hr
  · change squareFaceParameter j (sourceCrossCoordinates (sourceCollarPiece i j x))/
        (1-sourceCollarTime (sourceCollarPiece i j x))=x 2
    rw [sourceCollarPiece_cross i j ht' ha hb,squareFace_parameter,
      sourceCollarPiece_time i j ht' ha hb]
    exact mul_div_cancel_left₀ _ hq

lemma sourceCollarPiece_injOn (i j : Fin 4) :
    InjOn (sourceCollarPiece i j)
      {x : Fin 3 → ℝ | x 0∈Ico 0 1 ∧ |x 1|≤1 ∧ |x 2|≤1} := by
  intro x hx y hy he
  apply_fun sourceCollarInverse i j at he
  rwa [sourceCollarInverse_left i j hx.1 hx.2.1 hx.2.2,
    sourceCollarInverse_left i j hy.1 hy.2.1 hy.2.2] at he

def sourceCollarBox (η : ℝ) : Set (Fin 3 → ℝ) := Icc ![0,-1,-1] ![η,1,1]

lemma mem_sourceCollarBox {η : ℝ} {x : Fin 3 → ℝ} :
    x∈sourceCollarBox η ↔ x 0∈Icc 0 η ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
  simp [sourceCollarBox,mem_Icc,Pi.le_def,Fin.forall_fin_succ,abs_le]
  tauto

lemma sourceCollarBox_measurable (η : ℝ) : MeasurableSet (sourceCollarBox η) := measurableSet_Icc
lemma sourceCollarBox_compact (η : ℝ) : IsCompact (sourceCollarBox η) := isCompact_Icc

lemma sourceCollarBox_injOn (i j : Fin 4) {η : ℝ} (hη : η<1) :
    InjOn (sourceCollarPiece i j) (sourceCollarBox η) := by
  apply (sourceCollarPiece_injOn i j).mono
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceCollarBox.mp hx
  exact ⟨⟨ht.1,ht.2.trans_lt hη⟩,ha,hb⟩

lemma sourceCollarDerivative_det (i j : Fin 4) (x : Fin 3 → ℝ) :
    (sourceCollarDerivative i j x).det =
      -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0) := by
  change LinearMap.det (Matrix.toLin' (sourceCollarJacobian i j x))=_
  rw [LinearMap.det_toLin',sourceCollarJacobian_det]

lemma sourceCollar_jacobian_bounds (i j : Fin 4) {η : ℝ} (hη : η<1)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarBox η) :
    sourceLength*sourceHole*sourceRadialWidth*(1-η) ≤ abs ((sourceCollarDerivative i j x).det) ∧
    abs ((sourceCollarDerivative i j x).det) ≤ sourceLength*sourceRadialWidth := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceCollarBox.mp hx
  have htr : x 0∈Icc 0 1 := ⟨ht.1,(ht.2.trans hη.le)⟩
  have hr := sourceCollarRadius_bounds j htr hb
  have hL : 0 ≤ sourceLength := by norm_num [sourceLength]
  have hw : 0 ≤ sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hd : 0 ≤ sourceHole := by norm_num [sourceHole]
  have hrr : 0 ≤ sourceCollarRadius j (x 0) (x 2) := hd.trans hr.1
  have hq : 0 ≤ 1-x 0 := sub_nonneg.mpr htr.2
  rw [sourceCollarDerivative_det]
  have he : -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)=
      -(sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  constructor
  · exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr.1 hL) hw)
      (by linarith [ht.2]) (by linarith) (by positivity)
  · calc
      _ ≤ sourceLength*1*sourceRadialWidth*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr.2 hL) hw)
          (by linarith [ht.1]) hq (by positivity)
      _=_ := by ring

theorem sourceCollar_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i j : Fin 4) {η : ℝ} (hη : η<1) (g : (Fin 3 → ℝ) → F) :
    (∫ y in sourceCollarPiece i j '' sourceCollarBox η,g y)=
      ∫ x in sourceCollarBox η,
        (sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)) •
          g (sourceCollarPiece i j x) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (sourceCollarBox_measurable η)
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
    (sourceCollarBox_injOn i j hη)]
  apply setIntegral_congr_fun (sourceCollarBox_measurable η)
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceCollarBox.mp hx
  dsimp only
  rw [sourceCollarDerivative_det]
  have hr := (sourceCollarRadius_bounds j ⟨ht.1,ht.2.trans hη.le⟩ hb).1
  have hd : 0 ≤ sourceHole := by norm_num [sourceHole]
  have hL : 0 ≤ sourceLength := by norm_num [sourceLength]
  have hw : 0 ≤ sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hrr : 0 ≤ sourceCollarRadius j (x 0) (x 2) := hd.trans hr
  have hq : 0 ≤ 1-x 0 := by linarith [ht.2]
  have he : -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)=
      -(sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]

lemma sourceCollarPiece_lipschitz (i j : Fin 4) (η : ℝ) :
    ∃ C : NNReal,LipschitzOnWith C (sourceCollarPiece i j) (sourceCollarBox η) := by
  exact (sourceCollarPiece_contDiff i j).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) (sourceCollarBox_compact η)

end ScalarConductivity

end

end OAI
