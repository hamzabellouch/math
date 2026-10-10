import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.HellingerDistance
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ObservableDistance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteLawDistance
open Classical Matrix MeasureTheory

noncomputable def smoothNoiseTransportError {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) : ℝ :=
  2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot*(matrixHSNorm (C-B)^2+
    ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2))

theorem finiteAffineNoiseLaw_close {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    ObservableClose (finiteAffineNoiseLaw (1+B) a) (finiteAffineNoiseLaw (1+C) (a+h))
      (smoothNoiseTransportError B C h) := by
  rw [finiteAffineNoiseLaw_density _ _ (Matrix.PosDef.one.add_posSemidef hB).det_pos,
    finiteAffineNoiseLaw_density _ _ (Matrix.PosDef.one.add_posSemidef hC).det_pos]
  have hf : ContDiff ℝ 1 smoothNoiseRoot := smoothNoiseRoot_contDiff.of_le (by norm_num)
  have hp := affineNoiseRoot_continuous smoothNoiseRoot_contDiff.continuous (1+B) a
  have hq := affineNoiseRoot_continuous smoothNoiseRoot_contDiff.continuous (1+C) (a+h)
  have hh := (observableClose_of_density (volume : Measure (ι → ℝ))
    (hq.pow 2).measurable (hp.pow 2).measurable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (affineNoiseRoot_integrable_square smoothNoiseRoot_contDiff.continuous smoothNoiseRoot_compact
      _ _ (one_add_psd_isUnit_det C hC))
    (affineNoiseRoot_integrable_square smoothNoiseRoot_contDiff.continuous smoothNoiseRoot_compact
      _ _ (one_add_psd_isUnit_det B hB))).symm
  apply hh.mono
  exact affineNoiseDensity_L1_distance hf smoothNoiseRoot_compact
    smoothNoiseRoot_normalized smoothNoiseRoot_even B C hB hC a h

end FiniteLawDistance

section FiniteField
open Classical Matrix MeasureTheory

noncomputable def finiteCoefficientField {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun z => a z+x z+∑w∈J,B z w*x w

theorem finiteCoefficientField_measurable {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) : Measurable (finiteCoefficientField J a B) := by
  apply Measurable.of_eval
  intro z
  exact (measurable_const.add (measurable_pi_apply z)).add
    (Finset.measurable_sum _ (fun w _ => measurable_const.mul (measurable_pi_apply w)))

noncomputable def joinedNoiseField {ι : Type*} (J : Finset ι) (q : ℝ)
    (x : (J → ℝ) × ({z : ι // z∉J} → ℝ)) : ι → ℝ :=
  fun z => if hz : z∈J then x.1 ⟨z,hz⟩ else q+x.2 ⟨z,hz⟩

theorem joinedNoiseField_measurable {ι : Type*} (J : Finset ι) (q : ℝ) :
    Measurable (joinedNoiseField J q) := by
  apply Measurable.of_eval
  intro z
  by_cases hz : z∈J
  · simpa only [joinedNoiseField,dite_eq_left hz,Function.comp_def] using
      (measurable_pi_apply (⟨z,hz⟩ : J)).comp measurable_fst
  · simp only [joinedNoiseField,dite_eq_right hz]
    fun_prop

theorem finiteCoefficientField_law {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (q : ℝ)
    (ha : ∀z,z∉J → a z=q) (hB : ∀z,z∉J → ∀w,B z w=0) :
    (independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B)=
      ((finiteAffineNoiseLaw (1+(B.submatrix (fun z : J => z.val) (fun z : J => z.val)))
        (fun z : J => a z)).prod (independentSmoothNoiseLaw {z : ι // z∉J})).map
          (joinedNoiseField J q) := by
  let e := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun z => z∈J)).symm
  have hsplit : (independentSmoothNoiseLaw ι)=
      ((independentSmoothNoiseLaw J).prod (independentSmoothNoiseLaw {z : ι // z∉J})).map e := by
    convert! (infinitePi_split smoothNoiseLaw (fun z => z∈J)).symm using 1
    congr 2
    apply MeasurableEquiv.ext
    funext x
    funext z
    by_cases hz : z∈J <;> simp [e,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,hz]
  rw [hsplit,Measure.map_map (finiteCoefficientField_measurable J a B) e.measurable]
  let A : Matrix J J ℝ := 1+B.submatrix (fun z : J => z.val) (fun z : J => z.val)
  let f : (J → ℝ) → (J → ℝ) := fun x => (fun z : J => a z)+A*ᵥx
  have hf : Measurable f := by fun_prop
  change _=((independentSmoothNoiseLaw J).map f |>.prod
    (independentSmoothNoiseLaw {z : ι // z∉J})).map (joinedNoiseField J q)
  have hid : (independentSmoothNoiseLaw {z : ι // z∉J}).map id=
      independentSmoothNoiseLaw {z : ι // z∉J} := Measure.map_id
  conv_rhs => rw [← hid]
  rw [Measure.map_prod_map _ _ hf measurable_id,
    Measure.map_map (joinedNoiseField_measurable J q) (hf.prodMap measurable_id)]
  congr 1
  ext x z
  have he (w : ι) : e x w=(if hw : w∈J then x.1 ⟨w,hw⟩ else x.2 ⟨w,hw⟩) := rfl
  have hs : (∑w : J,B z w*x.1 w)=∑w∈J,B z w*e x w := by
    rw [← Finset.sum_coe_sort J (fun w => B z w*e x w)]
    apply Finset.sum_congr rfl
    intro w _
    rw [he,dite_eq_left w.property]
  by_cases hz : z∈J
  · change a z+e x z+(∑w∈J,B z w*e x w)=joinedNoiseField J q (f x.1,x.2) z
    simp only [joinedNoiseField,dite_eq_left hz,f,A,Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply]
    change a z+e x z+(∑w∈J,B z w*e x w)=a z+(x.1 ⟨z,hz⟩+∑w : J,B z w*x.1 w)
    rw [hs,he,dite_eq_left hz,add_assoc]
  · simp only [Function.comp_apply,finiteCoefficientField,joinedNoiseField,dite_eq_right hz,
      Prod.map_snd,id_eq,he,ha z hz,hB z hz,zero_mul,Finset.sum_const_zero,add_zero]

end FiniteField

section WholeFieldDistance
open Classical Matrix MeasureTheory

theorem finiteCoefficientField_close {ι : Type*} (J : Finset ι)
    (a b : ι → ℝ) (B C : Matrix ι ι ℝ) (q : ℝ)
    (ha : ∀z,z∉J → a z=q) (hb : ∀z,z∉J → b z=q)
    (hBr : ∀z,z∉J → ∀w,B z w=0) (hCr : ∀z,z∉J → ∀w,C z w=0)
    (hB : B.PosSemidef) (hC : C.PosSemidef) :
    ObservableClose
      ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B))
      ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J b C))
      (smoothNoiseTransportError (B.submatrix (fun z : J => z.val) (fun z : J => z.val))
        (C.submatrix (fun z : J => z.val) (fun z : J => z.val))
        (fun z : J => b z-a z)) := by
  rw [finiteCoefficientField_law J a B q ha hBr,finiteCoefficientField_law J b C q hb hCr]
  have hh := finiteAffineNoiseLaw_close
    (B.submatrix (fun z : J => z.val) (fun z : J => z.val))
    (C.submatrix (fun z : J => z.val) (fun z : J => z.val))
    (hB.submatrix _) (hC.submatrix _) (fun z : J => a z) (fun z : J => b z-a z)
  have he : (fun z : J => a z)+(fun z : J => b z-a z)=(fun z : J => b z) := by ext z; simp
  rw [he] at hh
  convert! (hh.prod_right (independentSmoothNoiseLaw {z : ι // z∉J})).map
    (joinedNoiseField_measurable J q) using 1 <;> congr!

noncomputable def smoothNoiseTransportConstant : ℝ :=
  2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)+1

theorem smoothNoiseTransportConstant_pos : 0<smoothNoiseTransportConstant := by
  unfold smoothNoiseTransportConstant
  positivity

theorem smoothNoiseTransportError_le {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (h : ι → ℝ) :
    smoothNoiseTransportError B C h ≤ smoothNoiseTransportConstant*
      (matrixHSNorm (C-B)+(1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh)) := by
  let d := matrixHSNorm (C-B)
  let v := (1+d)*finiteL2Norm ((1+B)⁻¹*ᵥh)
  have hd : 0≤d := matrixHSNorm_nonneg _
  have hv : 0≤v := mul_nonneg (by linarith) (finiteL2Norm_nonneg _)
  have hC := affineNoiseEnergyConstant_nonneg smoothNoiseRoot
  have hs : Real.sqrt (d^2+v^2) ≤ d+v := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  unfold smoothNoiseTransportError
  rw [Real.sqrt_mul hC]
  change 2*(Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)*Real.sqrt (d^2+v^2))≤_
  calc
    _ ≤ (2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot))*(d+v) := by
      nlinarith [Real.sqrt_nonneg (affineNoiseEnergyConstant smoothNoiseRoot)]
    _ ≤ _ := by
      unfold smoothNoiseTransportConstant
      change _ ≤ (2*Real.sqrt (affineNoiseEnergyConstant smoothNoiseRoot)+1)*(d+v)
      nlinarith

end WholeFieldDistance

end SimpleAmenable
end
end

end OAI
