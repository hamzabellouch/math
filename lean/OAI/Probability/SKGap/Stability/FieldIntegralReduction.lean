import Mathlib
import OAI.Probability.SKGap.Localization.CubeApprox
import OAI.Probability.SKGap.Localization.LocalVolumeChange
import OAI.Probability.SKGap.Matrix.ConditionalMiddleNorm
import OAI.Probability.SKGap.Gaussian.GaussianReductionPointwise

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal
attribute [local fun_prop] continuous_radialDensity

def fieldMollifier {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Fin n → ℝ) : ℝ :=
  radialDensity σ (tapField j J h y)*exp ((n:ℝ)*j*(1-overlap y)^2/2)

def fieldIntegral {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ∫⁻ y in E, ENNReal.ofReal (fieldMollifier j σ J h y)

lemma continuous_fieldMollifier {n : ℕ} (j σ : ℝ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ))=>
      fieldMollifier j σ p.1 p.2.1 p.2.2) := by
  unfold fieldMollifier tapField onsager overlap magnetization
  exact ((continuous_radialDensity σ).comp (by fun_prop)).mul (by fun_prop)

def conditionalFieldWeight {n : ℕ} [NeZero n] (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (y : Fin n → ℝ) : ℝ≥0∞ :=
  conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y) (empiricalObservation j t σ y)
    {W | (W,y) ∈ E}

lemma field_noise_convolution {n : ℕ} [NeZero n] {j t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    (y : Fin n → ℝ) (f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞) (g : MatrixCoordinates (Fin n) → ℝ) :
      (∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)
        ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))=
      ENNReal.ofReal (exp ((n:ℝ)*j*(1-overlap y)^2/2))*
        (ENNReal.ofReal (radialDensity (sqrt (t+σ^2))
          (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))*
            f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := by
    simp only [fieldMollifier,tapField_planted_observation j t σ,
      ENNReal.ofReal_mul (radialDensity_pos hσ _).le]
    rw [lintegral_mul_const _ (by fun_prop),lintegral_mul_const _ (by fun_prop),gaussian_radial_convolution ht hσ]
    ring

theorem field_reduction_fixed {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) (y : Fin n → ℝ) :
    (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        E.indicator (fun _=>1) ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞ := fun W=>E.indicator (fun _=>1) (W,y)
  have hf : Measurable f := measurable_const.indicator (hE.preimage (by fun_prop))
  change (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ _ _ y)*f _ ∂_ ∂_)=_
  simp_rw [field_noise_convolution ht hσ y f]
  have hgf : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := hf.comp (by unfold goeMatrix; fun_prop)
  have hgr : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => ENNReal.ofReal
      (radialDensity (sqrt (t+σ^2)) (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))) := by
    apply Measurable.ennreal_ofReal
    apply (continuous_radialDensity _).measurable.comp
    unfold Matrix.mulVec dotProduct goeMatrix
    fun_prop
  erw [lintegral_const_mul _ (hgr.mul hgf),goe_pointwise_conditional_integral
    (div_nonneg hj (Nat.cast_nonneg n)) (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) _ _ f hf]
  have hfi : (∫⁻ W,f W ∂conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y)
      (empiricalObservation j t σ y))=conditionalFieldWeight j t σ E y := by
    change (∫⁻ W, {W | (W,y)∈E}.indicator (fun _=>(1 : ℝ≥0∞)) W ∂_)=_
    have hset : MeasurableSet {W : (Fin n×Fin n) → ℝ | (W,y)∈E} := hE.preimage (by fun_prop)
    rw [lintegral_indicator hset,lintegral_const]
    simp [conditionalFieldWeight]
  rw [hfi,← mul_assoc,← ENNReal.ofReal_mul (exp_pos _).le]
  congr 1
  congr 1
  rw [mul_comm,scalar_density_cancellation hj ht hσ y]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

lemma fieldMollifier_eq_localAction {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : fieldMollifier j σ J h y=
      ((sqrt (2*Real.pi)*σ)⁻¹)^n*exp (localAction j σ J h y) := by
  unfold fieldMollifier radialDensity localAction varianceAverage
  rw [Fintype.card_fin,vectorNorm_sq,mul_assoc,← exp_add]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma fieldIntegral_eq_localVolume {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (E : Set (Field n)) :
    fieldIntegral j σ J h E=localVolume j σ J h E := by
  unfold fieldIntegral localVolume
  simp_rw [fieldMollifier_eq_localAction,ENNReal.ofReal_mul (by positivity : 0 ≤ ((sqrt (2*Real.pi)*σ)⁻¹)^n)]
  exact lintegral_const_mul _ (Real.measurable_exp.comp (localAction_continuous j σ J h).measurable |>.ennreal_ofReal)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma outer_add_rank_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v w z : ι → ℝ) : (vecMulVec u v+vecMulVec w z).rank ≤ 2 := by
  let Q : Matrix ι (Fin 2) ℝ := fun i k=>![u i,w i] k
  let R : Matrix (Fin 2) ι ℝ := fun k i=>![v i,z i] k
  have he : vecMulVec u v+vecMulVec w z=Q*R := by
    ext i k
    change u i*v k+w i*z k=∑ l : Fin 2,Q i l*R l k
    simp [Q,R,Fin.sum_univ_two]
  rw [he]
  exact (rank_mul_le_left Q R).trans (by simpa using rank_le_card_width Q)

lemma operator_outer_vector_le {n : ℕ} (u v : Field n) :
    opNorm (vecMulVec u v) ≤ vectorNorm u*vectorNorm v :=
  operator_vecMulVec_le (WithLp.toLp 2 u) (WithLp.toLp 2 v)

lemma vectorNorm_const_one (n : ℕ) : vectorNorm (fun _ : Fin n=>(1:ℝ))=sqrt (n:ℝ) := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (sqrt_nonneg _)).mp
  rw [vectorNorm_sq,sq_sqrt (Nat.cast_nonneg _)]
  simp [vectorSqNorm]

lemma spinVariance_norm_bound {n : ℕ} (y : Field n) :
    vectorNorm (spinVariance y) ≤ sqrt (n:ℝ) := by
  apply vectorNorm_le_of_sq_sum (sqrt_nonneg _)
  rw [sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _=>by
      have h0 := (spinVariance_pos y i).le
      have h1 := spinVariance_le_one y i
      nlinarith)
    _ = _ := by simp

lemma weightedMagnetization_norm_bound {n : ℕ} (y : Field n) :
    vectorNorm (fun i=>magnetization y i*spinVariance y i) ≤ sqrt (n:ℝ) := by
  have hh := vectorNorm_diag_le zero_le_one (x := magnetization y)
    (a := spinVariance y) (fun i=>(abs_of_pos (spinVariance_pos y i)).trans_le (spinVariance_le_one y i))
  simpa only [one_mul,mul_comm] using hh.trans (by simpa only [one_mul] using magnetization_norm_bound y)

def plantedJacobianPerturbation {n : ℕ} (j : ℝ) (y : Field n) : Matrix (Fin n) (Fin n) ℝ :=
  (-j/(n:ℝ)) • vecMulVec (fun _=>1) (spinVariance y)+
  (-2*j/(n:ℝ)) • vecMulVec (magnetization y) (fun i=>magnetization y i*spinVariance y i)

lemma plantedJacobianPerturbation_rank {n : ℕ} (j : ℝ) (y : Field n) :
    (plantedJacobianPerturbation j y).rank ≤ 2 := by
  have he : plantedJacobianPerturbation j y=
    vecMulVec (fun _=>-j/(n:ℝ)) (spinVariance y)+
    vecMulVec (fun i=>(-2*j/(n:ℝ))*magnetization y i) (fun i=>magnetization y i*spinVariance y i) := by
    ext i k
    simp [plantedJacobianPerturbation,vecMulVec_apply,mul_assoc]
  rw [he]
  exact outer_add_rank_le_two _ _ _ _

lemma plantedJacobianPerturbation_norm {n : ℕ} (hn : 0 < n) {j : ℝ} (hj : 0 ≤ j) (y : Field n) :
    opNorm (plantedJacobianPerturbation j y) ≤ 3*j := by
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : opNorm (vecMulVec (fun _ : Fin n=>1) (spinVariance y)) ≤ (n:ℝ) := by
    apply (operator_outer_vector_le _ _).trans
    rw [vectorNorm_const_one]
    exact (mul_le_mul_of_nonneg_left (spinVariance_norm_bound y) (sqrt_nonneg _)).trans_eq (mul_self_sqrt hn0.le)
  have h2 : opNorm (vecMulVec (magnetization y) (fun i=>magnetization y i*spinVariance y i)) ≤ (n:ℝ) := by
    apply (operator_outer_vector_le _ _).trans
    exact (mul_le_mul (magnetization_norm_bound y) (weightedMagnetization_norm_bound y)
      (vectorNorm_nonneg _) (sqrt_nonneg _)).trans_eq (mul_self_sqrt hn0.le)
  have hh := real_opNorm_add ((-j/(n:ℝ)) • vecMulVec (fun _=>1) (spinVariance y))
    ((-2*j/(n:ℝ)) • vecMulVec (magnetization y) (fun i=>magnetization y i*spinVariance y i))
  change opNorm (plantedJacobianPerturbation j y) ≤ _ at hh
  simp only [real_opNorm_smul,abs_div,abs_of_pos hn0,abs_neg,abs_of_nonneg hj] at hh
  have hab : |-(2:ℝ)*j|=2*j := by rw [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_of_nonneg hj]
  rw [hab] at hh
  apply hh.trans
  have ha := mul_le_mul_of_nonneg_left h1 (div_nonneg hj hn0.le)
  have hb := mul_le_mul_of_nonneg_left h2 (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hj) hn0.le)
  have he1 : j/(n:ℝ)*(n:ℝ)=j := div_mul_cancel₀ j hn0.ne'
  have he2 : 2*j/(n:ℝ)*(n:ℝ)=2*j := div_mul_cancel₀ (2*j) hn0.ne'
  rw [he1] at ha
  rw [he2] at hb
  linarith

lemma fieldJacobian_planted_formula {n : ℕ} (hn : 0 < n) (j : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (y : Field n) :
    fieldJacobian j (plantedInteraction j W) y=
    1+((j*coordAverage (spinVariance y)) • 1-W)*diagonal (spinVariance y)+
      plantedJacobianPerturbation j y := by
  have hb : coordAverage (spinVariance y)=1-overlap y := by
    simpa only [coordAverage,Fintype.card_fin,varianceAverage] using (varianceAverage_eq_average hn y).symm
  ext i k
  simp only [Matrix.add_apply]
  erw [Matrix.mul_diagonal]
  simp only [fieldJacobian,hessianCore,plantedInteraction,plantedJacobianPerturbation,
    Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,hb,onsager,
    Matrix.one_apply]
  by_cases he : i=k <;> simp only [he,↓reduceIte] <;> ring
end SKGap
end
end

end OAI
