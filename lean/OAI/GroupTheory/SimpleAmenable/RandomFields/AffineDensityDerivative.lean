import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.MatrixInverseCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineDensityDerivative
open Classical Matrix
open scoped Matrix.Norms.Elementwise

noncomputable def affineNoiseRoot {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (A : Matrix ι ι ℝ) (a y : ι → ℝ) : ℝ :=
  noiseTensor (fun _ : ι => f) (A⁻¹*ᵥ(y-a))/Real.sqrt A.det

theorem inverse_affine_hasDerivAt {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hunit : IsUnit (A t).det) (y : ι → ℝ) :
    HasDerivAt (fun s => (A s)⁻¹*ᵥ(y-a s))
      (-(((A t)⁻¹*A')*ᵥ((A t)⁻¹*ᵥ(y-a t))+(A t)⁻¹*ᵥa')) t := by
  have h := matrix_hasDerivAt_mulVec (matrix_hasDerivAt_inverse hA hunit)
    ((hasDerivAt_const t y).sub ha)
  convert! h using 1
  simp only [zero_sub,Matrix.mulVec_neg,Matrix.neg_mulVec,Matrix.mulVec_mulVec,
    neg_mul,neg_add_rev]
  abel

theorem inverse_sqrt_det_hasDerivAt {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hpos : 0<(A t).det) :
    HasDerivAt (fun s => (Real.sqrt (A s).det)⁻¹)
      (-(Real.sqrt (A t).det)⁻¹*Matrix.trace ((A t)⁻¹*A')/2) t := by
  have hd := matrix_hasDerivAt_det hA (isUnit_iff_ne_zero.mpr hpos.ne')
  have hs := (hd.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
  convert! hs using 1
  rw [Matrix.trace_mul_comm A' (A t)⁻¹]
  have hh := Real.sq_sqrt hpos.le
  field_simp
  rw [hh]
  ring

theorem affineNoiseRoot_hasDerivAt {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hpos : 0<(A t).det) (y : ι → ℝ) :
    HasDerivAt (fun s => affineNoiseRoot f (A s) (a s) y)
      (-affineNoiseGenerator f ((A t)⁻¹*A') ((A t)⁻¹*ᵥa')
        ((A t)⁻¹*ᵥ(y-a t))/Real.sqrt (A t).det) t := by
  have hx := inverse_affine_hasDerivAt hA ha (isUnit_iff_ne_zero.mpr hpos.ne') y
  have hF := noiseTensor_hasDerivAt hf hx
  have hh := hF.mul (inverse_sqrt_det_hasDerivAt hA hpos)
  convert! hh using 1
  rw [affineNoiseGenerator_eq]
  simp only [Pi.neg_apply,Pi.add_apply,neg_mul,Finset.sum_neg_distrib]
  ring

end AffineDensityDerivative

section AffineDensityEnergy
open Classical Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem affineNoiseRoot_normalized {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : (∫x : ℝ,f x^2)=1)
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hpos : 0<A.det) :
    (∫y : ι → ℝ,affineNoiseRoot f A a y^2)=1 := by
  simp only [affineNoiseRoot,div_pow,Real.sq_sqrt hpos.le]
  rw [integral_div,integral_matrix_affine_inverse A a
    (isUnit_iff_ne_zero.mpr hpos.ne') (fun x => noiseTensor (fun _ : ι => f) x^2)]
  have ht : (∫x : ι → ℝ,noiseTensor (fun _ : ι => f) x^2)=1 := by
    rw [show (volume : Measure (ι → ℝ))=Measure.pi (fun _ : ι => (volume : Measure ℝ)) from rfl,
      noiseTensor_energy]
    simp only [hf,Finset.prod_const_one]
  rw [ht,mul_one,abs_of_pos hpos,div_self hpos.ne']

theorem affineNoiseRoot_derivative_energy {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {a' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (ha : HasDerivAt a a' t)
    (hpos : 0<(A t).det) :
    (∫y : ι → ℝ,deriv (fun s => affineNoiseRoot f (A s) (a s) y) t^2)≤
      affineNoiseEnergyConstant f*((∑i,∑j,((A t)⁻¹*A') i j^2)+
        ∑i,((A t)⁻¹*ᵥa') i^2) := by
  have hd (y : ι → ℝ) := (affineNoiseRoot_hasDerivAt (hf.differentiable (by norm_num))
    hA ha hpos y).deriv
  simp_rw [hd,div_pow,neg_sq,Real.sq_sqrt hpos.le]
  rw [integral_div,integral_matrix_affine_inverse (A t) (a t)
    (isUnit_iff_ne_zero.mpr hpos.ne')
    (fun x => affineNoiseGenerator f ((A t)⁻¹*A') ((A t)⁻¹*ᵥa') x^2),
    abs_of_pos hpos,mul_div_cancel_left₀ _ hpos.ne']
  exact affineNoiseGenerator_energy hf hc he hn _ _

end AffineDensityEnergy

end SimpleAmenable
end
end

end OAI
