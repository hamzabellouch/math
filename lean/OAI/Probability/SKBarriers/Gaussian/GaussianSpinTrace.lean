import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianResponse
import OAI.Probability.SKBarriers.SpinGlass.SpinCurvature
import OAI.Probability.SKBarriers.Calculus.CoordinateStein
import OAI.Probability.SKBarriers.Hierarchy.CascadeProbability

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
namespace SK.Analytic

section Trace
variable {I : Type} [Fintype I] [DecidableEq I]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix I I ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A*B).trace := by
  let S := CFC.sqrt A
  have hS : Sᴴ = S := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSS : S*S = A := by simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  rw [trace_mul_cycle,hS,hSS] at h
  exact h

theorem trace_mul_mono_of_posSemidef {A B C : Matrix I I ℝ}
    (hA : A.PosSemidef) (hBC : (C-B).PosSemidef) : (A*B).trace ≤ (A*C).trace := by
  have h := trace_mul_nonneg_of_posSemidef hA hBC
  rw [mul_sub,trace_sub] at h
  linarith

theorem posSemidef_trace_one_sub {A : Matrix I I ℝ} (hA : A.PosSemidef) :
    (A.trace • (1 : Matrix I I ℝ)-A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hd : (diagonal (fun i => A.trace-hA.isHermitian.eigenvalues i)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i
    rw [sub_nonneg,hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have he : diagonal (fun i => A.trace-hA.isHermitian.eigenvalues i) =
      A.trace • (1 : Matrix I I ℝ)- diagonal hA.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i=j <;> simp [hij]
  have H := hd.mul_mul_conjTranspose_same (U : Matrix I I ℝ)
  rw [he,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one] at H
  have hu : (U : Matrix I I ℝ)*(U : Matrix I I ℝ)ᴴ = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  rw [hu] at H
  have hs : (U : Matrix I I ℝ)*diagonal hA.isHermitian.eigenvalues*
      (U : Matrix I I ℝ)ᴴ = A := by
    simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id,
      id_eq,Matrix.star_eq_conjTranspose,U] using hA.isHermitian.spectral_theorem.symm
  rwa [hs] at H

theorem posSemidef_scalar_one_sub {A : Matrix I I ℝ} (hA : A.PosSemidef)
    {T : ℝ} (hT : A.trace ≤ T) : (T • (1 : Matrix I I ℝ)-A).PosSemidef := by
  have H := (posSemidef_trace_one_sub hA).add
    (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hT))
  convert H using 1
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem trace_square_bound {C V : Matrix I I ℝ} {T a : ℝ}
    (hC : C.PosSemidef) (hV : V.PosSemidef)
    (hCT : (T • (1 : Matrix I I ℝ)-C).PosSemidef)
    (hCV : (V+a • (1 : Matrix I I ℝ)-C).PosSemidef)
    (htr : C.trace ≤ T) (ha : 0 ≤ a) :
    (C*C).trace ≤ T*V.trace+a*T := by
  have h₁ := trace_mul_mono_of_posSemidef hC hCV
  have h₂ := trace_mul_mono_of_posSemidef hV hCT
  simp only [mul_add,Matrix.mul_smul,mul_one,trace_add,trace_smul,smul_eq_mul] at h₁ h₂
  rw [trace_mul_comm V C] at h₂
  nlinarith [mul_le_mul_of_nonneg_left htr ha]

end Trace

section Covariance
variable {Ω I : Type} [MeasurableSpace Ω] [Fintype I]
  {μ : Measure Ω} [IsFiniteMeasure μ]

def covarianceMatrix (X : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ :=
  fun i j => cov[X i,X j;μ]

omit [Fintype I] [IsFiniteMeasure μ] in
theorem covarianceMatrix_isHermitian (X : I → Ω → ℝ) :
    (covarianceMatrix X μ).IsHermitian := by
  ext i j
  simp only [covarianceMatrix,conjTranspose_apply,star_trivial,covariance_comm]

theorem covarianceMatrix_posSemidef (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    (covarianceMatrix X μ).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨covarianceMatrix_isHermitian X,fun u => ?_⟩
  have hXu (i : I) : MemLp (fun ω => u i*X i ω) 2 μ := (hX i).const_mul _
  have he : (star u ⬝ᵥ covarianceMatrix X μ *ᵥ u) =
      cov[fun ω => ∑ i, u i*X i ω,fun ω => ∑ i, u i*X i ω;μ] := by
    rw [covariance_fun_sum_left hXu (memLp_finsetSum _ (fun i _ => hXu i))]
    simp_rw [covariance_fun_sum_right hXu (hXu _)]
    simp_rw [covariance_const_mul_left,covariance_const_mul_right]
    change (∑ i, u i * ∑ j, cov[X i, X j; μ]*u j) = _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,covariance_self (memLp_finsetSum _ (fun i _ => hXu i)).aemeasurable]
  exact variance_nonneg _ _

def crossCovarianceMatrix (X Y : I → Ω → ℝ) (μ : Measure Ω) : Matrix I I ℝ :=
  fun i j => cov[X i,Y j;μ]

omit [Fintype I] in

theorem covarianceMatrix_residual (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ) (q : ℝ) :
    covarianceMatrix (fun i ω => X i ω-q*Y i ω) μ =
      covarianceMatrix X μ - q • (crossCovarianceMatrix X Y μ + crossCovarianceMatrix Y X μ) +
      q^2 • covarianceMatrix Y μ := by
  ext i j
  simp only [covarianceMatrix,crossCovarianceMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [covariance_fun_sub_fun_sub (hX i) ((hY i).const_mul q)
      (hX j) ((hY j).const_mul q)]
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  ring

variable [DecidableEq I]

theorem covariance_stein_bound (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (D C : Matrix I I ℝ) (Δ x : ℝ) (hΔ : 0 < Δ) (hx : 0 < x)
    (hD : D.IsHermitian) (hDC : (D-x • C).PosSemidef)
    (hXY : ∀ i j, cov[X i,Y j;μ] = Δ*D i j)
    (hYY : covarianceMatrix Y μ = Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) :
    (covarianceMatrix X μ+(Δ*x^2)⁻¹ • (1 : Matrix I I ℝ)-C).PosSemidef := by
  have hr := covarianceMatrix_posSemidef (fun i ω => X i ω-(Δ*x)⁻¹*Y i ω)
    (fun i => (hX i).sub ((hY i).const_mul _))
  rw [covarianceMatrix_residual X Y hX hY,hYY] at hr
  have hdij (i j) : D j i = D i j := by
    have H := congrArg (fun M : Matrix I I ℝ => M i j) hD.eq
    simpa only [conjTranspose_apply,star_trivial] using H
  have he : covarianceMatrix X μ - (Δ*x)⁻¹ •
      (crossCovarianceMatrix X Y μ + crossCovarianceMatrix Y X μ) +
      ((Δ*x)⁻¹)^2 • (Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) =
      covarianceMatrix X μ - x⁻¹ • D + (Δ*x^2)⁻¹ • (1 : Matrix I I ℝ) := by
    ext i j
    simp only [crossCovarianceMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hXY,covariance_comm (Y i),hdij]
    field_simp [hΔ.ne',hx.ne']
    ring
  rw [he] at hr
  have H := hr.add (hDC.smul (inv_nonneg.mpr hx.le))
  convert H using 1
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp [hx.ne']
  ring

theorem conditional_covariance_trace_bound (X Y : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (D C : Matrix I I ℝ) (Δ x T : ℝ) (hΔ : 0 < Δ) (hx : 0 < x)
    (hD : D.IsHermitian) (hC : C.PosSemidef) (htr : C.trace ≤ T)
    (hDC : (D-x • C).PosSemidef)
    (hXY : ∀ i j, cov[X i,Y j;μ] = Δ*D i j)
    (hYY : covarianceMatrix Y μ = Δ • (1 : Matrix I I ℝ)+(Δ^2*x) • D) :
    (C*C).trace ≤ T*(covarianceMatrix X μ).trace+T/(Δ*x^2) := by
  have H := trace_square_bound hC (covarianceMatrix_posSemidef X hX)
    (posSemidef_scalar_one_sub hC htr)
    (covariance_stein_bound X Y hX hY D C Δ x hΔ hx hD hDC hXY hYY)
    htr (by positivity : 0 ≤ (Δ*x^2)⁻¹)
  simpa only [div_eq_mul_inv,mul_comm ((Δ*x^2)⁻¹)] using H

end Covariance
end SK.Analytic
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
section FiniteCovariance
variable {S I : Type} [Fintype S] [Fintype I]

def finiteMean (p : S → ℝ) (v : S → I → ℝ) : I → ℝ := ∑ s, p s • v s

def finiteCovariance (p : S → ℝ) (v : S → I → ℝ) : Matrix I I ℝ :=
  (∑ s, p s • vecMulVec (v s) (v s)) - vecMulVec (finiteMean p v) (finiteMean p v)

omit [Fintype I] in
theorem finiteMean_apply (p : S → ℝ) (v : S → I → ℝ) (i : I) :
    finiteMean p v i = ∑ s, p s*v s i := by simp only [finiteMean,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

omit [Fintype I] in
theorem finiteCovariance_apply (p : S → ℝ) (v : S → I → ℝ) (i j : I) :
    finiteCovariance p v i j = (∑ s, p s*v s i*v s j)-finiteMean p v i*finiteMean p v j := by
  simp only [finiteCovariance,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,mul_assoc]

omit [Fintype I] in

theorem finiteCovariance_centered (p : S → ℝ) (v : S → I → ℝ) (hp : ∑ s, p s = 1) :
    finiteCovariance p v = ∑ s, p s • vecMulVec (v s-finiteMean p v) (v s-finiteMean p v) := by
  ext i j
  rw [finiteCovariance_apply]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,Pi.sub_apply]
  have he (s : S) : p s*((v s i-finiteMean p v i)*(v s j-finiteMean p v j)) =
      p s*v s i*v s j-(p s*v s i)*finiteMean p v j-
        (p s*v s j)*finiteMean p v i+p s*(finiteMean p v i*finiteMean p v j) := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul,← finiteMean_apply,hp,one_mul]
  ring

theorem finiteCovariance_posSemidef (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) : (finiteCovariance p v).PosSemidef := by
  rw [finiteCovariance_centered p v hs]
  apply Matrix.posSemidef_sum
  intro s _
  apply Matrix.PosSemidef.smul _ (hp s)
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v s-finiteMean p v)

theorem finiteMean_dotProduct (p : S → ℝ) (v : S → I → ℝ) (u : I → ℝ) :
    u ⬝ᵥ finiteMean p v = ∑ s, p s*(u ⬝ᵥ v s) := by
  simp only [finiteMean,dotProduct_sum,dotProduct_smul,smul_eq_mul]

theorem finiteCovariance_quadratic (p : S → ℝ) (v : S → I → ℝ) (u : I → ℝ) :
    u ⬝ᵥ finiteCovariance p v *ᵥ u =
      (∑ s, p s*(u ⬝ᵥ v s)^2)-(∑ s, p s*(u ⬝ᵥ v s))^2 := by
  simp only [finiteCovariance,Matrix.sub_mulVec,dotProduct_sub,Matrix.sum_mulVec,
    dotProduct_sum,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,dotProduct_smul,
    smul_eq_mul,op_smul_eq_mul,finiteMean_dotProduct]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [dotProduct_comm (v s) u]
    ring
  · rw [dotProduct_comm (finiteMean p v) u,finiteMean_dotProduct]
    ring

theorem finiteCovariance_trace_le [DecidableEq I] (p : S → ℝ) (v : S → I → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1) (hv : ∀ s i, |v s i| ≤ 1) :
    (finiteCovariance p v).trace ≤ (Fintype.card I : ℝ) := by
  calc
    _ ≤ ∑ _ : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      change finiteCovariance p v i i ≤ 1
      rw [finiteCovariance_apply]
      have he : ∑ s, p s*v s i*v s i ≤ 1 := by
        calc
          _ = ∑ s, p s*(v s i)^2 := by apply Finset.sum_congr rfl; intro s _; ring
          _ ≤ ∑ s, p s*1 := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
            ((sq_le_one_iff_abs_le_one _).mpr (hv s i)) (hp s))
          _ = 1 := by simpa only [mul_one] using hs
      nlinarith [sq_nonneg (finiteMean p v i)]
    _ = _ := by simp
end FiniteCovariance
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem directionalGradient_coordinateVector (n : ℕ) (F : ParameterSpace n → ℝ)
    (u : Fin n → ℝ) (z : ParameterSpace n) :
    directionalGradient F (coordinateVector n u) z = ∑ i, u i*directionalGradient F (coordinateAxis n i) z := by
  simp only [directionalGradient,coordinateVector,map_sum,map_smul,smul_eq_mul]

theorem hessian_tilted_integrable (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (u v : ParameterSpace n) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ F) z v u)
      ((fiberGaussian n x).tilted (fun z => p*F z)) := by
  have he : (fun z => fderiv ℝ (fderiv ℝ F) z v u) =
      fun z => fderiv ℝ (directionalGradient F u) z v := by
    funext z
    rw [fderiv_directionalGradient F hF.1]
    rfl
  rw [he]
  apply ((hF.directionalGradient_bounds u).2.derivative_eval v).integrable_tilted_fiberGaussian n _ (hF.const_mul p)
  exact ((directionalGradient_contDiff F hF.1 u).continuous_fderiv (by norm_num)).clm_apply continuous_const

section CovQuadratic
variable {Ω I : Type} [MeasurableSpace Ω] [Fintype I] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem covarianceMatrix_quadratic (X : I → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (u : I → ℝ) :
    u ⬝ᵥ covarianceMatrix X μ *ᵥ u =
      cov[fun z => ∑ i, u i*X i z,fun z => ∑ i, u i*X i z;μ] := by
  have hXu (i : I) : MemLp (fun z => u i*X i z) 2 μ := (hX i).const_mul _
  rw [covariance_fun_sum_left hXu (memLp_finsetSum _ (fun i _ => hXu i))]
  simp_rw [covariance_fun_sum_right hXu (hXu _)]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right]
  change (∑ i, u i * ∑ j, cov[X i, X j;μ]*u j) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end CovQuadratic

theorem gaussianResponse_quadratic (n : ℕ) (F : ParameterSpace n → ℝ)
    (hF : BoundedDerivs F) (p x : ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ gaussianResponse n F p x *ᵥ u =
      (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateVector n u) (coordinateVector n u)
        ∂(fiberGaussian n x).tilted (fun z => p*F z)) +
      p*cov[directionalGradient F (coordinateVector n u),directionalGradient F (coordinateVector n u);
        (fiberGaussian n x).tilted (fun z => p*F z)] := by
  let μ := (fiberGaussian n x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability n _ (hF.const_mul p) x
  have hM : gaussianResponse n F p x =
      (Matrix.of (fun i j => ∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)) +
      p • covarianceMatrix (fun i => directionalGradient F (coordinateAxis n i)) μ := by rfl
  rw [hM,Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  congr 1
  · have hI (i j : Fin n) := hessian_tilted_integrable n F hF p x (coordinateAxis n i) (coordinateAxis n j)
    have he (z : ParameterSpace n) :
        fderiv ℝ (fderiv ℝ F) z (coordinateVector n u) (coordinateVector n u) =
        ∑ i, ∑ j, u i*(fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i)*u j) := by
      simp only [coordinateVector,map_sum,map_smul,_root_.sum_apply,
        _root_.smul_apply,smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [(hF.1.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (coordinateAxis n j) (coordinateAxis n i)]
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ((hI i j).mul_const _).const_mul _))]
    change (∑ i, u i*(∑ j, (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateAxis n j) (coordinateAxis n i) ∂μ)*u j)) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => ((hI i j).mul_const _).const_mul _),Finset.mul_sum]
    simp only [integral_const_mul,integral_mul_const]
    rfl
  · congr 1
    rw [covarianceMatrix_quadratic _ (fun i =>
      (hF.directionalGradient_bounds _).1.memLp_two_tilted_fiberGaussian n _ (hF.const_mul p)
        (directionalGradient_contDiff F hF.1 _).continuous x)]
    have he : directionalGradient F (coordinateVector n u) = fun z => ∑ i, u i*directionalGradient F (coordinateAxis n i) z := by
      funext z
      exact directionalGradient_coordinateVector n F u z
    rw [he]
end SK.Analytic
namespace SK.Analytic
section MixtureCovariance
variable {Ω S : Type} [MeasurableSpace Ω] [Fintype S] {μ : Measure Ω} [IsProbabilityMeasure μ]

def integratedWeights (P : Ω → S → ℝ) (μ : Measure Ω) (s : S) : ℝ := ∫ z, P z s ∂μ

omit [Fintype S] [IsProbabilityMeasure μ] in
theorem integratedWeights_nonneg (P : Ω → S → ℝ) (hP : ∀ z s, 0 ≤ P z s) (s : S) :
    0 ≤ integratedWeights P μ s := integral_nonneg (fun z => hP z s)

theorem integratedWeights_sum (P : Ω → S → ℝ) (hP : ∀ s, Integrable (fun z => P z s) μ)
    (hS : ∀ z, ∑ s, P z s = 1) : ∑ s, integratedWeights P μ s = 1 := by
  unfold integratedWeights
  rw [← integral_finsetSum _ (fun s _ => hP s)]
  simp only [hS,integral_const,probReal_univ,one_smul]

omit [IsProbabilityMeasure μ] in
theorem integral_weighted_sum (P : Ω → S → ℝ) (hP : ∀ s, Integrable (fun z => P z s) μ) (a : S → ℝ) :
    (∫ z, ∑ s, P z s*a s ∂μ) = ∑ s, integratedWeights P μ s*a s := by
  rw [integral_finsetSum _ (fun s _ => (hP s).mul_const _)]
  simp only [integral_mul_const,integratedWeights]

theorem integratedWeights_total_variance (P : Ω → S → ℝ)
    (hP : ∀ s, MemLp (fun z => P z s) 2 μ) (a : S → ℝ) :
    (∫ z, (∑ s, P z s*(a s)^2)-(∑ s, P z s*a s)^2 ∂μ) +
      cov[fun z => ∑ s, P z s*a s,fun z => ∑ s, P z s*a s;μ] =
      (∑ s, integratedWeights P μ s*(a s)^2)-(∑ s, integratedWeights P μ s*a s)^2 := by
  have hPI (s : S) := (hP s).integrable (by norm_num)
  have hA : MemLp (fun z => ∑ s, P z s*a s) 2 μ :=
    memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hB : Integrable (fun z => ∑ s, P z s*(a s)^2) μ :=
    integrable_finsetSum _ (fun s _ => (hPI s).mul_const _)
  rw [integral_sub hB hA.integrable_sq,covariance_eq_sub hA hA]
  simp only [Pi.mul_apply]
  rw [integral_weighted_sum P hPI,integral_weighted_sum P hPI]
  have he : (∫ z, (∑ s, P z s*a s)^2 ∂μ) =
      ∫ z, (∑ s, P z s*a s)*(∑ s, P z s*a s) ∂μ := by simp only [pow_two]
  rw [he]
  ring
end MixtureCovariance
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeFieldCurvature
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def cascadeLiftCLM : (n : ℕ) → E →L[ℝ] CascadeSpace E n
  | 0 => ContinuousLinearMap.id ℝ E
  | n+1 => (cascadeLiftCLM n).prod 0

@[simp]
theorem cascadeLiftCLM_apply (n : ℕ) (u : E) : cascadeLiftCLM (E := E) n u = cascadeLift n u := by
  induction n with
  | zero => rfl
  | succ n ih => change (cascadeLiftCLM (E := E) n u,0) = (cascadeLift n u,0); rw [ih]

theorem cascadeAffine_gradient_scaled (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (u : E) (a : ℝ)
    (g : S → ℝ) (hg : ∀ s, L s (cascadeLift n u) = a*g s) (z : E) :
    directionalGradient (cascadePressure n m (affineLogPartition c L)) u z =
      a*∑ s, cascadeSpinWeight n m c L z s*g s := by
  rw [directionalGradient,cascadeAffine_gradient,cascadeMoment_affineMoment]
  simp only [hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem cascadeAffine_curvature_scaled (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) {p : ℝ}
    (hl : p ≤ 1) (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (u : E) (a : ℝ) (g : S → ℝ) (hg : ∀ s, L s (cascadeLift n u) = a*g s) (z : E) :
    p*a^2*((∑ s, cascadeSpinWeight n m c L z s*(g s)^2) -
      (∑ s, cascadeSpinWeight n m c L z s*g s)^2) ≤
      fderiv ℝ (fderiv ℝ (cascadePressure n m (affineLogPartition c L))) z u u := by
  have H := (cascadeAffine_curvature n m c L hl hm hmu hmono z u).2
  simp_rw [cascadeMoment_affineMoment,hg] at H
  have h₁ : (∑ s, cascadeSpinWeight n m c L z s*(a*g s)^2) =
      a^2*∑ s, cascadeSpinWeight n m c L z s*(g s)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have h₂ : (∑ s, cascadeSpinWeight n m c L z s*(a*g s)) =
      a*∑ s, cascadeSpinWeight n m c L z s*g s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h₁,h₂] at H
  convert H using 1; ring
end CascadeFieldCurvature

section CoordinateFields
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem cascade_coordinates_field (N n : ℕ)
    (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ) (a : ℝ)
    (v : S → Fin N → ℝ)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i)
    (u : Fin N → ℝ) (s : S) :
    L s (cascadeLift n (coordinateVector N u)) = a*(u ⬝ᵥ v s) := by
  rw [← cascadeLiftCLM_apply]
  simp only [coordinateVector,map_sum,map_smul,smul_eq_mul,cascadeLiftCLM_apply,hv,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end CoordinateFields
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section GaussianSpinResponse
variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in

theorem gaussianResponse_mixture_domination (N : ℕ) (F : ParameterSpace N → ℝ)
    (hF : BoundedDerivs F) (p a x : ℝ) (P : ParameterSpace N → S → ℝ)
    (v : S → Fin N → ℝ)
    (hP : ∀ s, MemLp (fun z => P z s) 2 ((fiberGaussian N x).tilted (fun z => p*F z)))
    (hPpos : ∀ z s, 0 ≤ P z s) (hPsum : ∀ z, ∑ s, P z s = 1)
    (hG : ∀ u z, directionalGradient F (coordinateVector N u) z =
      a*∑ s, P z s*(u ⬝ᵥ v s))
    (hH : ∀ u z, p*a^2*((∑ s, P z s*(u ⬝ᵥ v s)^2)-(∑ s, P z s*(u ⬝ᵥ v s))^2) ≤
      fderiv ℝ (fderiv ℝ F) z (coordinateVector N u) (coordinateVector N u)) :
    (gaussianResponse N F p x - (p*a^2) •
      finiteCovariance (integratedWeights P ((fiberGaussian N x).tilted (fun z => p*F z))) v).PosSemidef := by
  let μ := (fiberGaussian N x).tilted (fun z => p*F z)
  let := fiberGaussian_tilted_probability N _ (hF.const_mul p) x
  have hPI (s : S) : Integrable (fun z => P z s) μ := (hP s).integrable (by norm_num)
  have hC := finiteCovariance_posSemidef (integratedWeights P μ) v
    (integratedWeights_nonneg P hPpos) (integratedWeights_sum P hPI hPsum)
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(gaussianResponse_isHermitian N F hF.1 p x).sub (hC.isHermitian.smul (by simp [IsSelfAdjoint])),fun u => ?_⟩
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  rw [gaussianResponse_quadratic N F hF,finiteCovariance_quadratic]
  let A : ParameterSpace N → ℝ := fun z => ∑ s, P z s*(u ⬝ᵥ v s)
  have hA : MemLp A 2 μ := memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hB : Integrable (fun z => ∑ s, P z s*(u ⬝ᵥ v s)^2) μ :=
    integrable_finsetSum _ (fun s _ => (hPI s).mul_const _)
  have hv : Integrable (fun z => (∑ s, P z s*(u ⬝ᵥ v s)^2)-A z^2) μ := hB.sub hA.integrable_sq
  have HI := integral_mono (hv.const_mul (p*a^2))
    (hessian_tilted_integrable N F hF p x _ _) (hH u)
  rw [integral_const_mul] at HI
  have HT := integratedWeights_total_variance (μ := μ) P hP (fun s => u ⬝ᵥ v s)
  have he : directionalGradient F (coordinateVector N u) = fun z => a*A z := funext (hG u)
  rw [he,covariance_const_mul_left,covariance_const_mul_right]
  change 0 ≤ (∫ z, fderiv ℝ (fderiv ℝ F) z (coordinateVector N u) (coordinateVector N u) ∂μ) +
    p*(a*(a*cov[A,A;μ])) - (p*a^2)*
      ((∑ s, integratedWeights P μ s*(u ⬝ᵥ v s)^2)-(∑ s, integratedWeights P μ s*(u ⬝ᵥ v s))^2)
  change (∫ z, (∑ s, P z s*(u ⬝ᵥ v s)^2)-A z^2 ∂μ) + cov[A,A;μ] = _ at HT
  rw [← HT]
  nlinarith [HI]

theorem cascadeGaussianResponse_domination (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ)
    (p a x : ℝ) (hl : p ≤ 1) (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i) :
    let F := cascadePressure n m (affineLogPartition c L)
    let μ := (fiberGaussian N x).tilted (fun z => p*F z)
    let P := cascadeSpinWeight n m c L
    (gaussianResponse N F p x - (p*a^2) • finiteCovariance (integratedWeights P μ) v).PosSemidef := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  apply gaussianResponse_mixture_domination N F hF p a x (cascadeSpinWeight n m c L) v
  · intro s
    have hr := cascadeSpinWeight_regular n m c L s
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian N _ (hF.const_mul p) hr.1 x
  · exact cascadeSpinWeight_nonneg n m c L
  · exact cascadeSpinWeight_sum n m c L
  · intro u z
    exact cascadeAffine_gradient_scaled n m c L (coordinateVector N u) a _ (cascade_coordinates_field N n L a v hv u) z
  · intro u z
    exact cascadeAffine_curvature_scaled n m c L hl hm hmu hmono (coordinateVector N u) a _
      (cascade_coordinates_field N n L a v hv u) z
end GaussianSpinResponse
end SK.Analytic
namespace SK.Analytic
open Matrix
open scoped MatrixOrder
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section GaussianSpinTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem cascadeGaussian_conditional_trace (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (ParameterSpace N) n →L[ℝ] ℝ)
    (p a x : ℝ) (hp : 0 < p) (ha : 0 < a) (hl : p ≤ 1)
    (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, L s (cascadeLift n (coordinateAxis N i)) = a*v s i) :
    let F := cascadePressure n m (affineLogPartition c L)
    let μ := (fiberGaussian N x).tilted (fun z => p*F z)
    let P := cascadeSpinWeight n m c L
    let C := finiteCovariance (integratedWeights P μ) v
    let X := fun i z => finiteMean (P z) v i
    (C*C).trace ≤ (N : ℝ)*(covarianceMatrix X μ).trace+(N : ℝ)/(a^2*p^2) := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  let μ := (fiberGaussian N x).tilted (fun z => p*F z)
  let P := cascadeSpinWeight n m c L
  let C := finiteCovariance (integratedWeights P μ) v
  let X : Fin N → ParameterSpace N → ℝ := fun i z => finiteMean (P z) v i
  let Y : Fin N → ParameterSpace N → ℝ := fun i z => a*coordinateProjection N i z
  let D : Matrix (Fin N) (Fin N) ℝ := (a^2)⁻¹ • gaussianResponse N F p x
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  let := fiberGaussian_tilted_probability N _ (hF.const_mul p) x
  have hP (s : S) : MemLp (fun z => P z s) 2 μ := by
    have hr := cascadeSpinWeight_regular n m c L s
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian N _ (hF.const_mul p) hr.1 x
  have hPI (s : S) : Integrable (fun z => P z s) μ := (hP s).integrable (by norm_num)
  have hq₀ := integratedWeights_nonneg (μ := μ) P (cascadeSpinWeight_nonneg n m c L)
  have hq₁ := integratedWeights_sum (μ := μ) P hPI (cascadeSpinWeight_sum n m c L)
  have hC : C.PosSemidef := finiteCovariance_posSemidef _ v hq₀ hq₁
  have hCT : C.trace ≤ (N : ℝ) := by
    simpa only [Fintype.card_fin,C] using finiteCovariance_trace_le _ v hq₀ hq₁ hvb
  have hX (i : Fin N) : MemLp (X i) 2 μ := by
    change MemLp (fun z => finiteMean (P z) v i) 2 μ
    simp only [finiteMean_apply]
    exact memLp_finsetSum _ (fun s _ => (hP s).mul_const _)
  have hY (i : Fin N) : MemLp (Y i) 2 μ :=
    ((HasExpGrowth.linear (coordinateProjection N i)).memLp_two_tilted_fiberGaussian N _
      (hF.const_mul p) (coordinateProjection N i).continuous x).const_mul a
  have hG (i : Fin N) : directionalGradient F (coordinateAxis N i) = fun z => a*X i z := by
    funext z
    simpa only [X,P,finiteMean_apply] using cascadeAffine_gradient_scaled n m c L (coordinateAxis N i) a (fun s => v s i) (fun s => hv s i) z
  have hXG (i : Fin N) : X i = fun z => a⁻¹*directionalGradient F (coordinateAxis N i) z := by
    rw [hG]
    funext z
    simp only [inv_mul_cancel_left₀ ha.ne']
  have hD : D.IsHermitian := (gaussianResponse_isHermitian N F hF.1 p x).smul (by simp [IsSelfAdjoint])
  have hDC : (D-p • C).PosSemidef := by
    have H := (cascadeGaussianResponse_domination N n m c L p a x hl hm hmu hmono v hv).smul
      (inv_nonneg.mpr (sq_nonneg a))
    convert H using 1
    ext i j
    simp only [D,C,F,P,μ,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    field_simp [ha.ne']
  have hXY (i j : Fin N) : cov[X i,Y j;μ] = a^2*D i j := by
    rw [hXG]
    change cov[fun z => a⁻¹*directionalGradient F (coordinateAxis N i) z,
      fun z => a*coordinateProjection N j z;μ] = _
    rw [covariance_const_mul_left,covariance_const_mul_right,gaussian_tilted_cross_covariance N F hF p x]
    simp only [D,Matrix.smul_apply,smul_eq_mul]
    field_simp [ha.ne']
  have hYY : covarianceMatrix Y μ = a^2 • (1 : Matrix (Fin N) (Fin N) ℝ)+((a^2)^2*p) • D := by
    ext i j
    change cov[fun z => a*coordinateProjection N i z,fun z => a*coordinateProjection N j z;μ] = _
    rw [covariance_const_mul_left,covariance_const_mul_right,gaussian_tilted_field_covariance N F hF p x]
    simp only [D,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    field_simp [ha.ne']
  exact conditional_covariance_trace_bound X Y hX hY D C (a^2) p N (sq_pos_of_pos ha) hp hD hC hCT hDC hXY hYY
end GaussianSpinTrace
end SK.Analytic

end
end
end
end

end

end OAI
