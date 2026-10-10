import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AffineGeneratorIntegrability

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section HellingerDistance
open Classical MeasureTheory

theorem integral_abs_mul_le_sqrt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫x,|f x| *|g x| ∂μ)≤ Real.sqrt (∫x,f x^2 ∂μ)*Real.sqrt (∫x,g x^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (by
    apply Real.holderConjugate_iff.mpr
    norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hf) (by simpa using hg)
  norm_num only [ENNReal.ofReal_ofNat,Real.norm_eq_abs,Real.rpow_ofNat,abs_sq,
    one_div,← Real.sqrt_eq_rpow] at h
  simpa only [sq_abs] using h

theorem density_L1_le_twice_root_distance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {R S : X → ℝ} (hR : MemLp R 2 μ) (hS : MemLp S 2 μ)
    (hnR : (∫x,R x^2 ∂μ)=1) (hnS : (∫x,S x^2 ∂μ)=1) :
    (∫x,|R x^2-S x^2| ∂μ)≤2*Real.sqrt (∫x,(R x-S x)^2 ∂μ) := by
  have hab := integral_abs_mul_le_sqrt μ (hR.sub hS) (hR.add hS)
  have heq (x : X) : |R x^2-S x^2|=|R x-S x| *|R x+S x| := by
    rw [← abs_mul]
    congr 1
    ring
  simp only [Pi.sub_apply,Pi.add_apply] at hab
  have hi : (∫x,(R x+S x)^2 ∂μ)≤4 := by
    calc
      _ ≤ ∫x,2*(R x^2+S x^2) ∂μ := integral_mono (hR.add hS).integrable_sq
        ((hR.integrable_sq.add hS.integrable_sq).const_mul 2)
        (fun x => by
          change (R x+S x)^2≤2*(R x^2+S x^2)
          nlinarith [sq_nonneg (R x-S x)])
      _ = 4 := by
        rw [integral_const_mul,integral_add hR.integrable_sq hS.integrable_sq,hnR,hnS]
        norm_num
  simp_rw [heq]
  apply hab.trans
  have hh : Real.sqrt (∫x,(R x+S x)^2 ∂μ)≤2 := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num at *; exact hi⟩
  nlinarith [Real.sqrt_nonneg (∫x,(R x-S x)^2 ∂μ)]

end HellingerDistance

section AffineDensityDistance
open Classical Matrix MeasureTheory Set

theorem affineNoiseRoot_memLp {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    MemLp (affineNoiseRoot f A a) 2 (volume : Measure (ι → ℝ)) := by
  apply (memLp_two_iff_integrable_sq (affineNoiseRoot_continuous hf A a).aestronglyMeasurable).mpr
  exact affineNoiseRoot_integrable_square hf hc A a hA

theorem affineNoiseRoot_square_distance {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    (∫y : ι → ℝ,(affineNoiseRoot f (1+C) (a+h) y-affineNoiseRoot f (1+B) a y)^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2) := by
  have hR (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      MemLp (noiseInterpolationRoot f B C a h t) 2 (volume : Measure (ι → ℝ)) :=
    affineNoiseRoot_memLp hf.continuous hc _ _
      (one_add_psd_isUnit_det _ (covarianceSegment_posSemidef B C hB hC ht))
  have H := rootPath_energy_distance (volume : Measure (ι → ℝ))
    (noiseInterpolationRoot f B C a h) (noiseInterpolationDerivative f B C a h)
    (affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
      ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2))
    (noiseInterpolationDerivative_measurable hf B C a h)
    (fun t ht y => noiseInterpolation_hasDerivAt hf B C hB hC a h y ht)
    (fun y => noiseInterpolationDerivative_continuousOn hf B C hB hC a h y)
    (fun t ht => affineNoiseRootDerivative_integrable_square hf hc _ _ _ _
      (one_add_psd_isUnit_det _ (covarianceSegment_posSemidef B C hB hC ht)))
    (fun t ht => noiseInterpolationDerivative_energy hf hc hn he B C hB hC a h ht)
    ((hR 1 (by norm_num)).sub (hR 0 (by norm_num))).integrable_sq
  simpa only [noiseInterpolationRoot,covarianceSegment,sub_self,zero_smul,add_zero,
    zero_add,one_smul,sub_zero] using H

theorem affineNoiseDensity_L1_distance {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ) :
    (∫y : ι → ℝ,|affineNoiseRoot f (1+C) (a+h) y^2-affineNoiseRoot f (1+B) a y^2|)≤
      2*Real.sqrt (affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2)) := by
  have H := density_L1_le_twice_root_distance (volume : Measure (ι → ℝ))
    (affineNoiseRoot_memLp hf.continuous hc (1+C) (a+h) (one_add_psd_isUnit_det C hC))
    (affineNoiseRoot_memLp hf.continuous hc (1+B) a (one_add_psd_isUnit_det B hB))
    (affineNoiseRoot_normalized hn (1+C) (a+h) (Matrix.PosDef.one.add_posSemidef hC).det_pos)
    (affineNoiseRoot_normalized hn (1+B) a (Matrix.PosDef.one.add_posSemidef hB).det_pos)
  exact H.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (affineNoiseRoot_square_distance hf hc hn he B C hB hC a h)) (by norm_num))

end AffineDensityDistance

section FiniteAffineLaw
open Classical MeasureTheory Matrix Set
open scoped ENNReal

theorem measurableEquiv_map_withDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e=(μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply,MeasurableEquiv.symm_apply_apply] using
    (setLIntegral_map (μ := μ) hs (hf.comp e.symm.measurable) e.measurable).symm

theorem smoothNoiseLaw_pi_density (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι => smoothNoiseLaw)=
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) := by
  have hi : Integrable (fun x : ℝ => smoothNoiseRoot x^2) := by
    have hh := noiseFactor_integrable_product
      (smoothNoiseRoot_contDiff.of_le (by norm_num)) smoothNoiseRoot_compact .base .base
    simpa only [noiseFactor,pow_two] using hh
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻x,ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)
    ∂((Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (univ.pi s)))=_
  rw [Measure.restrict_pi_pi]
  have hint : Integrable (fun x : ι → ℝ => noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)
      (Measure.pi (fun i => (volume : Measure ℝ).restrict (s i))) := by
    simpa only [noiseTensor,← Finset.prod_pow] using Integrable.fintype_prod (fun i => hi.restrict (s := s i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => sq_nonneg _))]
  have he : (∫x : ι → ℝ,noiseTensor (fun _ : ι => smoothNoiseRoot) x^2
      ∂Measure.pi (fun i => (volume : Measure ℝ).restrict (s i)))=
      ∏i,∫t : ℝ,smoothNoiseRoot t^2 ∂(volume.restrict (s i)) := by
    simp only [noiseTensor,← Finset.prod_pow]
    convert! integral_fintype_prod_eq_prod
      (μ := fun i => (volume : Measure ℝ).restrict (s i))
      (fun (_ : ι) (x : ℝ) => smoothNoiseRoot x^2) using 1
  rw [he,ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [smoothNoiseLaw,withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi.restrict (s := s i)) (ae_of_all _ (fun _ => sq_nonneg _))

theorem independentSmoothNoiseLaw_finite_density (ι : Type*) [Fintype ι] :
    independentSmoothNoiseLaw ι=(volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) := by
  rw [independentSmoothNoiseLaw,Measure.infinitePi_eq_pi,smoothNoiseLaw_pi_density]

noncomputable def finiteAffineNoiseLaw {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : Measure (ι → ℝ) :=
  (independentSmoothNoiseLaw ι).map (fun x => a+A*ᵥx)

instance finiteAffineNoiseLaw_probability {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : IsProbabilityMeasure (finiteAffineNoiseLaw A a) := by
  unfold finiteAffineNoiseLaw
  infer_instance

theorem finiteAffineNoiseLaw_density {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hpos : 0<A.det) :
    finiteAffineNoiseLaw A a=(volume : Measure (ι → ℝ)).withDensity
      (fun y => ENNReal.ofReal (affineNoiseRoot smoothNoiseRoot A a y^2)) := by
  let hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hpos.ne'
  let e := matrixAffineEquiv A a hA
  have hf : Measurable (fun x : ι → ℝ => ENNReal.ofReal
      (noiseTensor (fun _ : ι => smoothNoiseRoot) x^2)) :=
    ((noiseTensor_continuous smoothNoiseRoot_contDiff.continuous).pow 2).measurable.ennreal_ofReal
  unfold finiteAffineNoiseLaw
  rw [independentSmoothNoiseLaw_finite_density]
  rw [show (fun x => a+A*ᵥx)=(e : (ι → ℝ) → (ι → ℝ)) from
    (funext (fun x => matrixAffineEquiv_apply A a x hA)).symm,
    measurableEquiv_map_withDensity _ e hf]
  have hm : Measure.map e volume=ENNReal.ofReal |A.det⁻¹| • volume := by
    rw [show (e : (ι → ℝ) → (ι → ℝ))=(fun x => a+A*ᵥx) from
      funext (fun x => matrixAffineEquiv_apply A a x hA),map_matrix_affine_volume A a hA]
  rw [hm,withDensity_smul_measure]
  have hr := withDensity_smul (μ := (volume : Measure (ι → ℝ)))
    (ENNReal.ofReal |A.det⁻¹|) (hf.comp e.symm.measurable)
  trans volume.withDensity
    (ENNReal.ofReal |A.det⁻¹| • (fun y => ENNReal.ofReal
      (noiseTensor (fun _ : ι => smoothNoiseRoot) (e.symm y)^2)))
  · convert! hr.symm using 1
  congr 1
  ext y
  simp only [Pi.smul_apply,smul_eq_mul,matrixAffineEquiv_symm_apply,e,
    affineNoiseRoot,div_pow,Real.sq_sqrt hpos.le]
  rw [abs_of_pos (inv_pos.mpr hpos),← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
  congr 1
  ring

end FiniteAffineLaw

end SimpleAmenable
end
end

end OAI
