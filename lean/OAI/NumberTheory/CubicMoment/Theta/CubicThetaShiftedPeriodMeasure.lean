import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedTorus

namespace OAI

/-! The actual period-nine cell and its exact volume normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaShiftedPeriodEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  cubicThetaPeriodEquiv.trans (complexMulEquiv 3 (by norm_num))

def cubicThetaShiftedHorizontalCell : Set ℂ :=
  (fun z : ℂ => 3*z) '' cubicThetaHorizontalCell

lemma cubicThetaShiftedPeriodEquiv_apply (x : Fin 2 → ℝ) :
    cubicThetaShiftedPeriodEquiv x=3*cubicThetaPeriodCell x := rfl

lemma cubicThetaShiftedHorizontalCell_measurable : MeasurableSet cubicThetaShiftedHorizontalCell :=
  (complexMulEquiv 3 (by norm_num)).toHomeomorph.measurableEmbedding.measurableSet_image'
    cubicThetaHorizontalCell_measurable

lemma cubicThetaShiftedHorizontalCell_compact_container :
    ∃ K : Set ℂ,IsCompact K ∧ cubicThetaShiftedHorizontalCell⊆K := by
  obtain ⟨K,hK,hcell⟩ := cubicThetaHorizontalCell_compact_container
  exact ⟨(fun z : ℂ => 3*z) '' K,hK.image (continuous_const.mul continuous_id),
    Set.image_mono hcell⟩

lemma cubicThetaShiftedPeriodEquiv_map_volume :
    Measure.map cubicThetaShiftedPeriodEquiv volume=
      ENNReal.ofReal (2/(81*Real.sqrt 3)) • (volume : Measure ℂ) := by
  have he : (cubicThetaShiftedPeriodEquiv : (Fin 2 → ℝ) → ℂ)=
      (fun z : ℂ => 3*z) ∘ cubicThetaPeriodEquiv := rfl
  rw [he,←Measure.map_map (by fun_prop) cubicThetaPeriodEquiv.continuous.measurable,
    cubicThetaPeriodEquiv_map_volume,Measure.map_smul _ (by fun_prop),
    complexMul_map_volume 3 (by norm_num),smul_smul]
  congr 1
  norm_num only [Complex.normSq_ofNat,ENNReal.ofReal_ofNat]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cubicThetaShiftedPeriodEquiv_preimage_cell :
    cubicThetaShiftedPeriodEquiv ⁻¹' cubicThetaShiftedHorizontalCell=
      {x : Fin 2 → ℝ | ∀ i,x i∈Ico (0:ℝ) 1} := by
  have hinj : Function.Injective (fun z : ℂ => 3*z) :=
    fun _ _ h => mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) h
  change cubicThetaPeriodEquiv ⁻¹'
    ((fun z : ℂ => 3*z) ⁻¹' ((fun z : ℂ => 3*z) '' cubicThetaHorizontalCell))=_
  rw [Set.preimage_image_eq _ hinj,cubicThetaPeriodEquiv_preimage_cell]

lemma cubicThetaShiftedHorizontalCell_integral (f : ℂ → ℂ) :
    (∫ z in cubicThetaShiftedHorizontalCell,f z)=
      (81*Real.sqrt 3/2:ℝ) •
        ∫ x in {x : Fin 2 → ℝ | ∀ i,x i∈Ico (0:ℝ) 1},f (3*cubicThetaPeriodCell x) := by
  have hi := setIntegral_map_equiv (μ:=volume)
    cubicThetaShiftedPeriodEquiv.toHomeomorph.toMeasurableEquiv f cubicThetaShiftedHorizontalCell
  change (∫ z in cubicThetaShiftedHorizontalCell,f z ∂Measure.map cubicThetaShiftedPeriodEquiv volume)=
    ∫ x in cubicThetaShiftedPeriodEquiv ⁻¹' cubicThetaShiftedHorizontalCell,
      f (cubicThetaShiftedPeriodEquiv x) at hi
  rw [cubicThetaShiftedPeriodEquiv_map_volume,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(81*Real.sqrt 3)),
    cubicThetaShiftedPeriodEquiv_preimage_cell] at hi
  have he : (81*Real.sqrt 3/2:ℝ)*(2/(81*Real.sqrt 3))=1 := by field_simp
  calc
    _ = (81*Real.sqrt 3/2:ℝ) • ((2/(81*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaShiftedHorizontalCell,f z) := by rw [smul_smul,he,one_smul]
    _ = _ := congrArg (fun w : ℂ => (81*Real.sqrt 3/2:ℝ) • w) hi

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaShiftedHorizontalCoefficient (f : ℂ → ℂ)
    (F : C(UnitAddTorus (Fin 2),ℂ)) (h : Eisenstein)
    (hf : ∀ x,f (3*cubicThetaPeriodCell x)=F (fun i => (x i:UnitAddCircle))) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*f z)=
      (81*Real.sqrt 3/2:ℝ) • cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h := by
  rw [cubicThetaShiftedHorizontalCell_integral,cubicThetaTorusCoefficient_integral,
    cubicThetaTorus_integral_cell]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [hf,cubicThetaTorusFourier_actual,cubicThetaShifted_frequency_cell]

lemma cubicThetaShiftedTorus_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ (cubicThetaShiftedTorus b v s)) h=
      ((2*Real.pi/(81*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
        cubicThetaShiftedFourierTerm b v s h := by
  let L := (cubicThetaTorusCoefficientMap h).comp (ContinuousMap.toLp 2 volume ℂ)
  rw [←cubicThetaTorusCoefficientMap_apply]
  change L (cubicThetaShiftedTorus b v s)=_
  rw [cubicThetaShiftedTorus,map_smul]
  simp only [L,ContinuousLinearMap.comp_apply,cubicThetaTorusCoefficientMap_apply,
    cubicThetaShiftedTorusSeries_coefficient b hv hs,smul_eq_mul]

lemma cubicThetaShiftedPeriod_fourier_constant :
    ((81*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(81*Real.sqrt 3):ℂ)=(Real.pi:ℂ) := by
  push_cast
  field_simp

theorem cubicThetaShifted_horizontal_coefficient (b : Eisenstein) {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    (∫ z in cubicThetaShiftedHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        cubicThetaEisenstein ((cubicThetaInversion 1 (z,v)).1+b,
          (cubicThetaInversion 1 (z,v)).2) s)=
      ((Real.pi:ℂ)/Complex.Gamma s)*(v:ℂ)^s*cubicThetaShiftedFrequencyDirichlet b h s*
        ∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  rw [cubicThetaShiftedHorizontalCoefficient _ (cubicThetaShiftedTorus b v s) h
    (fun x => (cubicThetaShiftedTorus_real b hv hs x).symm),
    cubicThetaShiftedTorus_coefficient b hv hs,Complex.real_smul]
  unfold cubicThetaShiftedFourierTerm
  calc
    _ = (((81*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(81*Real.sqrt 3):ℂ))*
      ((v:ℂ)^s/Complex.Gamma s)*cubicThetaShiftedFrequencyDirichlet b h s*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t) := by ring
    _ = _ := by rw [cubicThetaShiftedPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
