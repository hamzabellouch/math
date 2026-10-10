import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PolygonApproxIdentity
import OAI.GroupTheory.SimpleAmenable.RandomFields.AffineDensityDerivative

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoiseContinuity
open Classical Matrix MeasureTheory

@[fun_prop] theorem noiseTensor_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) : Continuous (noiseTensor (fun _ : ι => f)) := by
  unfold noiseTensor
  fun_prop

@[fun_prop] theorem noiseGradientCoordinate_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : ι) : Continuous (noiseGradientCoordinate f i) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hc := hf.continuous
  unfold noiseGradientCoordinate
  fun_prop

@[fun_prop] theorem affineNoiseGenerator_continuous_comp {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {L : X → Matrix ι ι ℝ} {v x : X → ι → ℝ}
    (hL : Continuous L) (hv : Continuous v) (hx : Continuous x) :
    Continuous (fun z => affineNoiseGenerator f (L z) (v z) (x z)) := by
  simp only [affineNoiseGenerator_eq]
  have hF := (noiseTensor_continuous hf.continuous).comp hx
  have hg (i : ι) := (noiseGradientCoordinate_continuous hf i).comp hx
  unfold Matrix.trace Matrix.diag Matrix.mulVec dotProduct
  fun_prop

@[fun_prop] theorem affineNoiseRoot_continuous {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Continuous f) (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    Continuous (affineNoiseRoot f A a) := by
  unfold affineNoiseRoot
  apply Continuous.div_const
  exact (noiseTensor_continuous hf).comp (by fun_prop)

local instance {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

local instance {ι : Type*} [Fintype ι] : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

theorem matrix_inverse_measurable {ι : Type*} [Fintype ι]
    {X : Type*} [MeasurableSpace X] {A : X → Matrix ι ι ℝ}
    (hA : Measurable A) : Measurable (fun x => (A x)⁻¹) := by
  have hd := continuous_id.matrix_det.measurable.comp hA
  have ha := continuous_id.matrix_adjugate.measurable.comp hA
  simp only [Matrix.inv_def,Ring.inverse_eq_inv]
  exact hd.inv.smul ha

theorem matrix_inverse_continuousAt {ι : Type*} [Fintype ι]
    {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι ℝ} {x : X}
    (hA : ContinuousAt A x) (hn : (A x).det≠0) : ContinuousAt (fun y => (A y)⁻¹) x := by
  apply (continuousAt_matrix_inv (A x) ?_).comp hA
  convert! (continuousAt_inv₀ hn) using 1
  ext x
  exact Ring.inverse_eq_inv x

end NoiseContinuity

section CovarianceResolvent
open Classical Matrix

noncomputable def matrixHSNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (∑i,∑j,A i j^2)

theorem matrixHSNorm_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    0≤ matrixHSNorm A := Real.sqrt_nonneg _

theorem matrixHSNorm_sq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    matrixHSNorm A^2=∑i,∑j,A i j^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j))))

theorem finiteL2Norm_matrix_mulVec {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteL2Norm (A*ᵥx)≤ matrixHSNorm A*finiteL2Norm x := by
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) (mul_nonneg (matrixHSNorm_nonneg _) (finiteL2Norm_nonneg _))).mp
  rw [mul_pow,matrixHSNorm_sq,finiteL2Norm_sq,finiteL2Norm_sq,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) x

theorem matrixHSNorm_inverse_contraction {ι : Type*} [Fintype ι]
    (B D : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    matrixHSNorm ((1+B)⁻¹*D)≤ matrixHSNorm D := by
  apply (sq_le_sq₀ (matrixHSNorm_nonneg _) (matrixHSNorm_nonneg _)).mp
  rw [matrixHSNorm_sq,matrixHSNorm_sq,Finset.sum_comm,Finset.sum_comm (f:=fun i j => D i j^2)]
  apply Finset.sum_le_sum
  intro j _
  have h := pow_le_pow_left₀ (finiteL2Norm_nonneg _) (finiteL2Norm_inverse_contraction B hB (fun i => D i j)) 2
  simpa only [finiteL2Norm_sq,Matrix.mul_apply,Matrix.mulVec,dotProduct] using h

noncomputable def covarianceSegment {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ := (1-t) • B+t • C

theorem covarianceSegment_posSemidef {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) : (covarianceSegment B C t).PosSemidef :=
  (hB.smul (sub_nonneg.mpr ht.2)).add (hC.smul ht.1)

theorem covarianceSegment_affine {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) : 1+covarianceSegment B C t=(1+B)+t • (C-B) := by
  unfold covarianceSegment
  module

theorem covarianceSegment_inverse_signal {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (h : ι → ℝ) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    finiteL2Norm ((1+covarianceSegment B C t)⁻¹*ᵥh)≤
      (1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh) := by
  let P := covarianceSegment B C t
  let x := (1+B)⁻¹*ᵥh
  let y := (1+P)⁻¹*ᵥ((C-B)*ᵥx)
  have hP := covarianceSegment_posSemidef B C hB hC ht
  have hx : (1+B)*ᵥx=h := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec]
  have he : (1+P)*ᵥx=h+t • ((C-B)*ᵥx) := by
    rw [show 1+P=(1+B)+t • (C-B) from covarianceSegment_affine B C t,
      Matrix.add_mulVec,Matrix.smul_mulVec,hx]
  have hi := congrArg (fun v => (1+P)⁻¹*ᵥv) he
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (one_add_psd_isUnit_det P hP),
    Matrix.one_mulVec,Matrix.mulVec_add,Matrix.mulVec_smul] at hi
  have hv : (1+P)⁻¹*ᵥh=x-t • y := by
    exact eq_sub_of_add_eq (Eq.symm hi)
  rw [hv]
  calc
    _ ≤ finiteL2Norm x+finiteL2Norm (t • y) := finiteL2Norm_sub _ _
    _ = finiteL2Norm x+t*finiteL2Norm y := by rw [finiteL2Norm_smul,abs_of_nonneg ht.1]
    _ ≤ finiteL2Norm x+finiteL2Norm y := by
      exact add_le_add le_rfl (mul_le_of_le_one_left (finiteL2Norm_nonneg y) ht.2)
    _ ≤ finiteL2Norm x+matrixHSNorm (C-B)*finiteL2Norm x := by
      apply add_le_add le_rfl
      exact (finiteL2Norm_inverse_contraction P hP _).trans (finiteL2Norm_matrix_mulVec _ _)
    _ = _ := by ring

end CovarianceResolvent

section RootPathEnergy
open Classical MeasureTheory Set

theorem square_integral_le_integral_square {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ) :
    (∫x,f x ∂μ)^2≤∫x,f x^2 ∂μ := by
  let c := ∫x,f x ∂μ
  have hz : 0≤∫x,(f x)^2-2*c*f x+c^2 ∂μ := by
    apply integral_nonneg
    intro x
    change (0:ℝ)≤f x^2-2*c*f x+c^2
    nlinarith [sq_nonneg (f x-c)]
  have hs : Integrable (fun x => f x^2-2*c*f x) μ := hf2.sub (hf.const_mul (2*c))
  rw [integral_add hs (integrable_const _),integral_sub hf2 (hf.const_mul (2*c)),
    integral_const_mul,integral_const] at hz
  simp only [probReal_univ,one_smul] at hz
  change 0≤(∫x,f x^2 ∂μ)-2*c*c+c^2 at hz
  change c^2≤∫x,f x^2 ∂μ
  nlinarith

theorem unitInterval_probability : IsProbabilityMeasure
    ((volume : Measure ℝ).restrict (Ioc 0 1)) := by
  constructor
  simp

theorem rootPath_energy_distance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (R D : ℝ → X → ℝ) (C : ℝ)
    (hDmeas : Measurable (Function.uncurry D))
    (hderiv : ∀t∈Icc (0:ℝ) 1,∀x,HasDerivAt (fun s => R s x) (D t x) t)
    (hDcont : ∀x,ContinuousOn (fun t => D t x) (Icc (0:ℝ) 1))
    (hDint : ∀t∈Icc (0:ℝ) 1,Integrable (fun x => D t x^2) μ)
    (henergy : ∀t∈Icc (0:ℝ) 1,(∫x,D t x^2 ∂μ)≤C)
    (hRint : Integrable (fun x => (R 1 x-R 0 x)^2) μ) :
    (∫x,(R 1 x-R 0 x)^2 ∂μ)≤C := by
  let ν := (volume : Measure ℝ).restrict (Ioc 0 1)
  let : IsProbabilityMeasure ν := unitInterval_probability
  have ht : ∀ᵐt∂ν,t∈Icc (0:ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨ht.1.le,ht.2⟩
  have hmeas : AEStronglyMeasurable (fun p : ℝ×X => D p.1 p.2^2) (ν.prod μ) :=
    (hDmeas.pow_const 2).aestronglyMeasurable
  have heint : Integrable (fun t => ∫x,D t x^2 ∂μ) ν := by
    apply (integrable_const C).mono' hmeas.integral_prod_right'
    filter_upwards [ht] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact henergy t ht
  have hj : Integrable (fun p : ℝ×X => D p.1 p.2^2) (ν.prod μ) := by
    apply (integrable_prod_iff hmeas).mpr
    constructor
    · filter_upwards [ht] with t ht
      exact hDint t ht
    · simpa only [Real.norm_eq_abs,abs_sq] using heint
  have hpoint (x : X) : (R 1 x-R 0 x)^2≤∫t,D t x^2 ∂ν := by
    have hd : IntervalIntegrable (fun t => D t x) volume 0 1 :=
      (hDcont x).intervalIntegrable_of_Icc (by norm_num)
    have hd2 : IntervalIntegrable (fun t => D t x^2) volume 0 1 :=
      ((hDcont x).pow 2).intervalIntegrable_of_Icc (by norm_num)
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht) x) hd
    have hc := square_integral_le_integral_square ν hd.1 hd2.1
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hf
    rw [← hf]
    exact hc
  calc
    _ ≤ ∫x,∫t,D t x^2 ∂ν ∂μ := integral_mono hRint hj.integral_prod_right hpoint
    _ = ∫t,∫x,D t x^2 ∂μ ∂ν := (integral_integral_swap hj).symm
    _ ≤ ∫_t,C ∂ν := integral_mono_ae heint (integrable_const _) (by
      filter_upwards [ht] with t ht
      exact henergy t ht)
    _ = C := by simp

end RootPathEnergy

end SimpleAmenable
end
end

end OAI
