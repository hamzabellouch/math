import Mathlib
import OAI.Probability.SKGap.Localization.LocalVolumeEnergy
import OAI.Probability.SKGap.Gaussian.ProductGaussianDensity

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma map_affine_matrix_volume {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    Measure.map (fun g : Field n => y+A*ᵥg) volume = ENNReal.ofReal |A.det⁻¹| • volume := by
  have he : (fun g : Field n => y+A*ᵥg) = (fun z => y+z) ∘ (fun g => A*ᵥg) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  change Measure.map (fun g => A*ᵥg) volume=_ at hm
  rw [hm,Measure.map_smul _ (by fun_prop),map_add_left_eq_self]

lemma affine_set_lintegral_le {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+A*ᵥg ∈ E) (f : Field n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g in B,f (y+A*ᵥg)) ≤ ENNReal.ofReal |A.det⁻¹| * ∫⁻ z in E,f z := by
  calc
    _ = ∫⁻ g,(B.indicator (fun g => f (y+A*ᵥg))) g := (lintegral_indicator hB _).symm
    _ ≤ ∫⁻ g,(E.indicator f) (y+A*ᵥg) := by
      apply lintegral_mono
      intro g
      by_cases hg : g ∈ B
      · simp only [indicator_of_mem hg, indicator_of_mem (hBE g hg),le_refl]
      · rw [indicator_of_notMem hg]
        exact bot_le
    _ = ∫⁻ z,E.indicator f z ∂Measure.map (fun g : Field n => y+A*ᵥg) volume :=
      (lintegral_map (hf.indicator hE) (by fun_prop)).symm
    _ = _ := by rw [map_affine_matrix_volume y A hA,lintegral_smul_measure,lintegral_indicator hE]; rfl

lemma gaussian_standard_density {n : ℕ} : gaussianCoordinates (Fin n) =
    (volume : Measure (Field n)).withDensity (fun g =>
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^(n:ℕ)*exp (-vectorNorm g^2/2))) := by
  rw [gaussianCoordinates,GaussianDensity.pi_gaussian_density (hv := fun _ => one_ne_zero)]
  congr 1
  funext g
  congr 1
  simp only [gaussianPDFReal,sub_zero,NNReal.coe_one,mul_one,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← exp_sum,← Finset.sum_div,
    ← Finset.sum_neg_distrib,vectorNorm_sq,vectorSqNorm]

lemma gaussian_tilt_cancellation {n : ℕ} {B : Set (Field n)} (hB : MeasurableSet B)
    (φ : Field n → ℝ) (hφ : Measurable φ) :
    (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) ∂gaussianCoordinates (Fin n)) =
    ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ∫⁻ g in B,ENNReal.ofReal (exp (φ g)) := by
  have hnorm : Measurable (vectorNorm (n := n)) := (continuous_vectorNorm n).measurable
  rw [gaussian_standard_density,restrict_withDensity hB,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have he (g : Field n) :
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n*exp (-vectorNorm g^2/2)) *
        ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) =
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ENNReal.ofReal (exp (φ g)) := by
    rw [← ENNReal.ofReal_mul (by positivity),mul_assoc,← exp_add]
    have hh : -vectorNorm g^2/2+(vectorNorm g^2/2+φ g)=φ g := by ring
    rw [hh,ENNReal.ofReal_mul (by positivity)]
  simp_rw [Pi.mul_apply,he]
  exact lintegral_const_mul _ (by fun_prop)

theorem local_volume_change_of_variables {n : ℕ} (y : Field n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.det ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+(σ • U)*ᵥg ∈ E) (φ : Field n → ℝ) (hφ : Measurable φ) :
    ENNReal.ofReal |U.det| *
      (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ (y+(σ • U)*ᵥg)))
        ∂gaussianCoordinates (Fin n)) ≤
    ENNReal.ofReal (((sqrt (2*Real.pi)*σ)⁻¹)^n) * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)) := by
  have hA : (σ • U).det ≠ 0 := by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hσ.ne') hU
  rw [gaussian_tilt_cancellation hB (fun g => φ (y+(σ • U)*ᵥg)) (hφ.comp (by fun_prop))]
  have hh := affine_set_lintegral_le y (σ • U) hA hB hE hBE (fun z => ENNReal.ofReal (exp (φ z))) (by fun_prop)
  calc
    _ ≤ ENNReal.ofReal |U.det| * (ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n)*
        (ENNReal.ofReal |(σ • U).det⁻¹| * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)))) := by gcongr
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Matrix.det_smul,Fintype.card_fin,abs_inv,abs_mul,abs_pow,abs_of_pos hσ,mul_inv]
      have hUd : |U.det| ≠ 0 := abs_ne_zero.mpr hU
      rw [mul_inv,mul_pow]
      simp only [← inv_pow]
      field_simp

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma conditional_lintegral_identity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : Set Ω} (hB : μ B ≠ 0) (f : Ω → ℝ≥0∞) :
    μ B*(∫⁻ x,f x ∂cond μ B)=∫⁻ x in B,f x ∂μ := by
  rw [ProbabilityTheory.cond,lintegral_smul_measure]
  change μ B*((μ B)⁻¹*(∫⁻ x in B,f x ∂μ))=_
  rw [← mul_assoc,ENNReal.mul_inv_cancel hB (measure_ne_top _ _),one_mul]

lemma whitening_logdet {n : ℕ} (U Q : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det ≠ 0) (hQ : 0 < Q.det) (he : U*Q*U=1) :
    log |U.det| = -log Q.det/2 := by
  have hd : |U.det|^2*Q.det=1 := by
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_one] at hh
    rw [sq_abs]
    nlinarith only [hh]
  have hh := congrArg log hd
  rw [log_mul (pow_ne_zero _ (abs_ne_zero.mpr hU)) hQ.ne',log_pow,log_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

def localAction {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h z : Field n) : ℝ :=
    -vectorNorm (tapField j J h z)^2/(2*σ^2)+(n:ℝ)*j*varianceAverage z^2/2

def localVolume {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (E : Set (Field n)) : ℝ≥0∞ :=
    ENNReal.ofReal (((sqrt (2*Real.pi)*σ)⁻¹)^n) *
      ∫⁻ z in E,ENNReal.ofReal (exp (localAction j σ J h z))

lemma localAction_continuous {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) : Continuous (localAction j σ J h) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).comp (continuous_tapField j J h)).pow 2 |>.neg |>.div_const _).add
    ((hb.pow 2 |>.const_mul _).div_const _)

theorem local_volume_quantitative {n : ℕ} (hn : 0 < n) {j K γ σ η ρ r ε₁ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {E : Set (Field n)} (hE : MeasurableSet E)
    (hball : ∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E)
    (hsmall : 2*σ/sqrt γ ≤ r)
    (hdet : log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁))
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) ≤
      localVolume j σ J h E := by
  let L := fieldJacobian j J y
  let Q := Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)
  obtain ⟨U,hUH,hUd,hUQ,hlin,hbound⟩ := localGaussian_whitening L hγ
  have hU : U.det ≠ 0 := isUnit_iff_ne_zero.mp hUd
  have hQ : 0 < Q.det := (regularizedGram_posDef L hγ).det_pos
  have hlog := whitening_logdet U Q hU hQ hUQ
  let μ := gaussianCoordinates (Fin n)
  let B := localGaussianBall n
  let l : ℝ := j*varianceAverage y^2/2-2*η-
    (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ
  have hjensen : exp ((n:ℝ)*l) ≤ ∫ g,exp (localExponent j σ J U h y g) ∂cond μ B := by
    exact (exp_le_exp.mpr (localGaussian_exponent_bound hn hj hK hγ hσ hη hρ
      J U hJ h y hUH hbound hlin hres)).trans (localGaussian_jensen hn j σ J U h y)
  have hp : ENNReal.ofReal (3/4:ℝ) ≤ μ B := by
    have hh := ENNReal.ofReal_le_ofReal (localGaussianBall_probability hn)
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hcond : ENNReal.ofReal (exp ((n:ℝ)*l)) ≤
      ∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B := by
    have hi : Integrable (fun g => exp (localExponent j σ J U h y g)) (cond μ B) :=
      localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal hjensen
  have hvol := local_volume_change_of_variables y U hU hσ (localGaussianBall_measurable n) hE
    (fun g hg => hball _ ((localGaussian_displacement hγ hσ.le hbound hg).trans
      (mul_le_mul_of_nonneg_right hsmall (sqrt_nonneg _))))
    (localAction j σ J h) (localAction_continuous _ _ _ _).measurable
  have hexp (g : Field n) : vectorNorm g^2/2+localAction j σ J h (y+(σ • U)*ᵥg)=
      localExponent j σ J U h y g := by unfold localAction localExponent; ring
  simp_rw [hexp] at hvol
  change ENNReal.ofReal |U.det| *(∫⁻ g in B,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂μ) ≤
    localVolume j σ J h E at hvol
  rw [← conditional_lintegral_identity (localGaussianBall_ne_zero hn)] at hvol
  have hscalar : (3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ)) ≤
      |U.det| *((3/4:ℝ)*exp ((n:ℝ)*l)) := by
    rw [← exp_log (abs_pos.mpr hU)]
    calc
      _ ≤ (3/4:ℝ)*exp (log |U.det|+(n:ℝ)*l) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        rw [hlog]
        change log Q.det ≤ _ at hdet
        dsimp [l]
        linarith only [hdet]
      _ = _ := by rw [exp_add]; ring
  calc
    _ ≤ ENNReal.ofReal (|U.det| *((3/4:ℝ)*exp ((n:ℝ)*l))) := ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal |U.det| *(ENNReal.ofReal (3/4:ℝ)*ENNReal.ofReal (exp ((n:ℝ)*l))) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal |U.det| *(μ B*(∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B)) := by
      gcongr
    _ ≤ _ := hvol

end SKGap
end
end

end OAI
