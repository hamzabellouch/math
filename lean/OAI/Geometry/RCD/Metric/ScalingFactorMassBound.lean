import OAI.Geometry.RCD.Heat.CompactKernelFactor

namespace OAI

/-! # Exact scaling normalization bounds the product of factor masses -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem scaling_factor_mass_bound (K : C(X × Y,ℝ)) (F : C(X,ℝ)) (G : C(Y,ℝ))
    {a : ℝ} (ha : 0<a) (hK : ∀ x y, a≤K (x,y))
    (hF : ∀ x, 0≤F x) (hG : ∀ y, 0≤G y)
    (hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1) :
    (∫ x, F x ∂μ)*(∫ y, G y ∂ν)≤1/a := by
  have hFi : Integrable F μ := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hGi : Integrable G ν := G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  have hKG (x : X) : Integrable (fun y => K (x,y)*G y) ν :=
    ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb (x : X) : a*(∫ y, G y ∂ν)≤∫ y, K (x,y)*G y ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono (hGi.const_mul a) (hKG x)
    intro y
    exact mul_le_mul_of_nonneg_right (hK x y) (hG y)
  have hp (x : X) : (a*(∫ y, G y ∂ν))*F x≤1 := by
    calc
      _ = F x*(a*(∫ y, G y ∂ν)) := by ring
      _ ≤ F x*(∫ y, K (x,y)*G y ∂ν) := mul_le_mul_of_nonneg_left (hb x) (hF x)
      _ = 1 := hrow x
  have hi := integral_mono (hFi.const_mul (a*(∫ y, G y ∂ν))) (integrable_const (1:ℝ)) hp
  rw [integral_const_mul] at hi
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,mul_one] at hi
  apply (le_div_iff₀ ha).mpr
  calc
    _ = (a*(∫ y, G y ∂ν))*(∫ x, F x ∂μ) := by ring
    _ ≤ 1 := hi

theorem scaling_pair_integral_bound (K : C(X × Y,ℝ)) (F : C(X,ℝ)) (G : C(Y,ℝ))
    {a A B : ℝ} (ha : 0<a) (hA : 0≤A) (hB : 0≤B)
    (hK : ∀ x y, a≤K (x,y)) (hF : ∀ x, 0≤F x) (hG : ∀ y, 0≤G y)
    (hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1)
    (k : C(X,ℝ)) (l : C(Y,ℝ)) (hl0 : ∀ y, 0≤l y)
    (hk : ∀ x, k x≤A) (hl : ∀ y, l y≤B) :
    (∫ x, k x*F x ∂μ)*(∫ y, l y*G y ∂ν)≤A*B/a := by
  have hFi : Integrable F μ := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hGi : Integrable G ν := G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  have hkFi : Integrable (fun x => k x*F x) μ :=
    (k.continuous.mul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlGi : Integrable (fun y => l y*G y) ν :=
    (l.continuous.mul G.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf : (∫ x, k x*F x ∂μ)≤A*(∫ x, F x ∂μ) := by
    rw [← integral_const_mul]
    exact integral_mono hkFi (hFi.const_mul A) (fun x => mul_le_mul_of_nonneg_right (hk x) (hF x))
  have hg : (∫ y, l y*G y ∂ν)≤B*(∫ y, G y ∂ν) := by
    rw [← integral_const_mul]
    exact integral_mono hlGi (hGi.const_mul B) (fun y => mul_le_mul_of_nonneg_right (hl y) (hG y))
  calc
    _ ≤ (A*(∫ x, F x ∂μ))*(B*(∫ y, G y ∂ν)) :=
      mul_le_mul hf hg (integral_nonneg fun y => mul_nonneg (hl0 y) (hG y))
        (mul_nonneg hA (integral_nonneg hF))
    _ = (A*B)*((∫ x, F x ∂μ)*(∫ y, G y ∂ν)) := by ring
    _ ≤ (A*B)*(1/a) := mul_le_mul_of_nonneg_left
      (scaling_factor_mass_bound μ ν K F G ha hK hF hG hrow) (mul_nonneg hA hB)
    _ = A*B/a := by ring

end RegularPointCoordinates

end

end OAI
