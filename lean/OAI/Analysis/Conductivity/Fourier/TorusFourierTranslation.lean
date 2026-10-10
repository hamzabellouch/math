import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma mFourier_spatial_add {d : Type*} [Fintype d] (h : d → ℤ)
    (x y : UnitAddTorus d) : mFourier h (x+y)=mFourier h x*mFourier h y := by
  simp only [mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    smul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourier_norm_one {d : Type*} [Fintype d] (h : d → ℤ)
    (x : UnitAddTorus d) : ‖mFourier h x‖=1 := by
  simp [mFourier,fourier_apply,norm_prod,Circle.norm_coe]

lemma mFourierCoeff_translation {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) (b : UnitAddTorus d) (h : d → ℤ) :
    mFourierCoeff (fun x => f (x+b)) h=mFourier h b*mFourierCoeff f h := by
  have hh := integral_add_right_eq_self (μ:=(volume : Measure (UnitAddTorus d)))
    (fun x => mFourier (-h) x*f x) b
  change (∫ x,mFourier (-h) x*f (x+b))=mFourier h b*(∫ x,mFourier (-h) x*f x)
  rw [←hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mFourier_spatial_add]
  have hz : mFourier h b*mFourier (-h) b=1 := by
    rw [←mFourier_add]
    simp only [add_neg_cancel,mFourier_zero,ContinuousMap.one_apply]
  calc
    _=mFourier (-h) x*f (x+b)*1 := by ring
    _=mFourier (-h) x*f (x+b)*(mFourier h b*mFourier (-h) b) := by rw [hz]
    _=_ := by ring

def torusCoordinateShift (j : Fin 2) (t : ℝ) : UnitAddTorus (Fin 2) :=
  fun i => if i=j then (t : UnitAddCircle) else 0

lemma mFourier_coordinateShift (h : Fin 2 → ℤ) (j : Fin 2) (t : ℝ) :
    mFourier h (torusCoordinateShift j t)=
      Complex.exp (2*Real.pi*Complex.I*(h j)*t) := by
  fin_cases j <;> simp [mFourier,torusCoordinateShift,Fin.prod_univ_two]

lemma mFourierCoeff_difference (f g : C(UnitAddTorus (Fin 2),ℂ)) (h : Fin 2 → ℤ) :
    mFourierCoeff (f-g) h=mFourierCoeff f h-mFourierCoeff g h := by
  unfold mFourierCoeff
  simp only [ContinuousMap.coe_sub,Pi.sub_apply,smul_sub]
  apply integral_sub
  · exact ((mFourier (-h)).continuous.smul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((mFourier (-h)).continuous.smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma torus_fourier_difference_bessel (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (t : ℝ) (s : Finset (Fin 2 → ℤ)) :
    ∑ h∈s,‖(Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*mFourierCoeff f h‖^2 ≤
      ∫ x : UnitAddTorus (Fin 2), ‖f (x+torusCoordinateShift j t)-f x‖^2 := by
  let g : C(UnitAddTorus (Fin 2),ℂ) :=
    (f.comp ⟨fun x => x+torusCoordinateShift j t,continuous_id.add continuous_const⟩)-f
  have hg (h : Fin 2 → ℤ) : mFourierCoeff g h=
      (Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*mFourierCoeff f h := by
    rw [mFourierCoeff_difference]
    change mFourierCoeff (fun x => f (x+torusCoordinateShift j t)) h-_=_
    rw [mFourierCoeff_translation,mFourier_coordinateShift]; ring
  have hlp := hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ g)
  have he : ∫ x : UnitAddTorus (Fin 2),‖(ContinuousMap.toLp 2 volume ℂ g : UnitAddTorus (Fin 2) → ℂ) x‖^2=
      ∫ x : UnitAddTorus (Fin 2),‖g x‖^2 := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜:=ℂ) (p:=2) volume g] with x hx
    rw [hx]
  rw [he] at hlp
  simp only [mFourierCoeff_toLp,hg] at hlp
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) hlp

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torus_phase_difference_limit (n : ℤ) :
    Tendsto (fun t : ℝ => ‖t⁻¹ •
      (Complex.exp (2*Real.pi*Complex.I*n*t)-1)‖^2) (𝓝[≠] (0:ℝ))
      (𝓝 ((2*Real.pi*(n:ℝ))^2)) := by
  have hd := (((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul
    (2*Real.pi*Complex.I*(n:ℂ))).cexp
  have hl := hd.tendsto_slope_zero.norm.pow 2
  simpa only [id_eq,zero_add,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
    mul_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,
    Complex.norm_intCast,mul_pow,sq_abs,norm_one,one_pow,one_mul,abs_one] using hl

lemma torus_difference_integral_bound (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|) (t : ℝ) :
    (∫ x : UnitAddTorus (Fin 2), ‖f (x+torusCoordinateShift j t)-f x‖^2)≤K^2*t^2 := by
  have hint : Integrable (fun x : UnitAddTorus (Fin 2) =>
      ‖f (x+torusCoordinateShift j t)-f x‖^2) volume :=
    ((f.continuous.comp (continuous_id.add continuous_const)).sub f.continuous).norm.pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _≤∫ _ : UnitAddTorus (Fin 2),(K*|t|)^2 := by
      apply integral_mono hint (integrable_const _)
      intro x
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (abs_nonneg t))).mpr (hf t x)
    _=K^2*t^2 := by simp [mul_pow,sq_abs]

lemma torus_coordinate_fourier_bound (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|)
    (s : Finset (Fin 2 → ℤ)) :
    ∑ h∈s,(2*Real.pi*(h j:ℝ))^2*‖mFourierCoeff f h‖^2≤K^2 := by
  have hl := tendsto_finsetSum s (fun h _ =>
    (torus_phase_difference_limit (h j)).mul_const (‖mFourierCoeff f h‖^2))
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t≠0 := ht
  have hb := (torus_fourier_difference_bessel f j t s).trans
    (torus_difference_integral_bound f j K hK hf t)
  have hs := mul_le_mul_of_nonneg_left hb (sq_nonneg t⁻¹)
  calc
    _=t⁻¹^2*∑ h∈s,‖(Complex.exp (2*Real.pi*Complex.I*(h j)*t)-1)*
        mFourierCoeff f h‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      simp only [norm_smul,Real.norm_eq_abs,norm_mul,mul_pow,sq_abs]
      ring
    _≤t⁻¹^2*(K^2*t^2) := hs
    _=K^2 := by field_simp

theorem torus_coordinate_fourier_summable (f : C(UnitAddTorus (Fin 2),ℂ))
    (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hf : ∀ t x,‖f (x+torusCoordinateShift j t)-f x‖≤K*|t|) :
    Summable (fun h : Fin 2 → ℤ => (2*Real.pi*(h j:ℝ))^2*‖mFourierCoeff f h‖^2) := by
  apply summable_of_sum_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact torus_coordinate_fourier_bound f j K hK hf

lemma torusCoordinateShift_norm (j : Fin 2) (t : ℝ) :
    ‖torusCoordinateShift j t‖≤|t| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro i
  dsimp only [torusCoordinateShift]
  split_ifs
  · exact QuotientAddGroup.norm_mk_le_norm
  · simp

lemma torus_lipschitz_coordinate_bound (f : C(UnitAddTorus (Fin 2),ℂ))
    (K : ℝ≥0) (hf : LipschitzWith K f) (j : Fin 2) (t : ℝ)
    (x : UnitAddTorus (Fin 2)) :
    ‖f (x+torusCoordinateShift j t)-f x‖≤(K:ℝ)*|t| := by
  have hh := hf.dist_le_mul (x+torusCoordinateShift j t) x
  rw [dist_eq_norm,dist_eq_norm,add_sub_cancel_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (torusCoordinateShift_norm j t) K.coe_nonneg)

end ScalarConductivity

end

end OAI
