import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourceCircleFourier

variable {ι κ : Type*}
noncomputable def meanC (f : AddCircle (1:ℝ) → ℂ) : ℂ :=
  ∫ θ, f θ ∂AddCircle.haarAddCircle
noncomputable def meanR (f : AddCircle (1:ℝ) → ℝ) : ℝ :=
  ∫ θ, f θ ∂AddCircle.haarAddCircle
noncomputable def poly (s : Finset ι) (w : ι → ℂ) (a : ι → ℤ)
    (θ : AddCircle (1:ℝ)) : ℂ := ∑ i ∈ s, w i * fourier (a i) θ

lemma continuous_poly (s : Finset ι) (w : ι → ℂ) (a : ι → ℤ) :
    Continuous (poly s w a) := by
  unfold poly
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (fourier (a i)).continuous

lemma mean_char (a : ℤ) : meanC (fourier a) = if a = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T:=1) a) 0
  simpa [fourierCoeff,meanC,Pi.single_apply,eq_comm] using h

lemma poly_mul (s : Finset ι) (t : Finset κ) (w : ι → ℂ)
    (v : κ → ℂ) (a : ι → ℤ) (b : κ → ℤ) (θ : AddCircle (1:ℝ)) :
    poly s w a θ * poly t v b θ =
      poly (s ×ˢ t) (fun ij => w ij.1*v ij.2) (fun ij => a ij.1+b ij.2) θ := by
  simp only [poly,sum_mul_sum,sum_product]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [fourier_add]
  ring

lemma mean_poly (s : Finset ι) (w : ι → ℂ) (a : ι → ℤ) :
    meanC (poly s w a) = ∑ i ∈ s, if a i = 0 then w i else 0 := by
  classical
  unfold meanC poly
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
    change (∑ i ∈ s, w i*meanC (fourier (a i))) = _
    simp only [mean_char,mul_ite,mul_one,mul_zero]
  · intro i hi
    exact (continuous_const.mul (fourier (a i)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma mean_poly_mul (s : Finset ι) (t : Finset κ) (w : ι → ℂ)
    (v : κ → ℂ) (a : ι → ℤ) (b : κ → ℤ) :
    meanC (fun θ => poly s w a θ * poly t v b θ) =
      ∑ i ∈ s, ∑ j ∈ t, if a i+b j = 0 then w i*v j else 0 := by
  classical
  simp_rw [poly_mul]
  rw [mean_poly,sum_product]

lemma conjugate_poly (s : Finset ι) (w : ι → ℂ) (a : ι → ℤ)
    (θ : AddCircle (1:ℝ)) :
    (starRingEnd ℂ) (poly s w a θ) =
      poly s (fun i => (starRingEnd ℂ) (w i)) (fun i => -a i) θ := by
  simp only [poly,map_sum,map_mul,fourier_neg]

lemma meanR_cast (f : AddCircle (1:ℝ) → ℝ) :
    (meanR f : ℂ) = meanC (fun θ => (f θ : ℂ)) := by
  exact integral_ofReal.symm

lemma energy_real (s : Finset ι) (w : ι → ℝ) (a : ι → ℤ) :
    meanR (fun θ => ‖poly s (fun i => (w i:ℂ)) a θ‖^2) =
      ∑ i ∈ s, ∑ j ∈ s, if a i = a j then w i*w j else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [meanR_cast]
  simp only [Complex.ofReal_pow,← Complex.mul_conj',Complex.ofReal_sum,
    apply_ite,Complex.ofReal_zero,Complex.ofReal_mul]
  simp_rw [conjugate_poly]
  rw [mean_poly_mul]
  simp only [← sub_eq_add_neg,sub_eq_zero,Complex.conj_ofReal]

lemma fourth_moment_real (s : Finset ι) (w : ι → ℝ) (a : ι → ℤ) :
    meanR (fun θ => ‖poly s (fun i => (w i:ℂ)) a θ‖^4) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ u ∈ s, ∑ v ∈ s,
        if a i+a j = a u+a v then (w i*w j)*(w u*w v) else 0 := by
  classical
  have hp (θ : AddCircle (1:ℝ)) :
      ‖poly s (fun i => (w i:ℂ)) a θ‖^4 =
      ‖poly (s ×ˢ s) (fun ij => ((w ij.1*w ij.2:ℝ):ℂ))
        (fun ij => a ij.1+a ij.2) θ‖^2 := by
    simp only [Complex.ofReal_mul]
    rw [← poly_mul s s (fun i => (w i:ℂ)) (fun i => (w i:ℂ)) a a,norm_mul]
    ring
  simp_rw [hp]
  rw [energy_real]
  simp only [sum_product]

lemma meanR_eq_interval (f : AddCircle (1:ℝ) → ℝ) :
    meanR f = ∫ θ in (0:ℝ)..1, f θ := by
  unfold meanR
  rw [AddCircle.integral_haarAddCircle]
  simpa using (AddCircle.intervalIntegral_preimage 1 0 f).symm

lemma poly_norm_le (s : Finset ι) (w : ι → ℂ) (a : ι → ℤ) (θ : AddCircle (1:ℝ)) :
    ‖poly s w a θ‖ ≤ ∑ i ∈ s, ‖w i‖ := by
  have hnorm (i : ι) : ‖(fourier (a i)) θ‖ = 1 := Circle.norm_coe _
  simpa only [poly,norm_mul,hnorm,mul_one] using
    norm_sum_le s (fun i => w i*fourier (a i) θ)

end OrdinaryCorrelations.SourceCircleFourier

end

end OAI
