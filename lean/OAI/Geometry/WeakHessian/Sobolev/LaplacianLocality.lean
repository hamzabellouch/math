import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.SquareSobolev
import OAI.Geometry.WeakHessian.LocalBounds.CoreAlgebra

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile165
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_zero_on_const_set (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ v : X → ℝ} (hχ : LocalSobolev m χ) (hv : LocalSobolev m v)
    {S : Set X} (hS : MeasurableSet S) {c : ℝ} (hc : ∀ᵐ x ∂m,x ∈ S → χ x=c) :
    ∀ᵐ x ∂m,x ∈ S → gamma m χ v x=0 := by
  have hcS : LocalSobolev m (fun _ : X => c) := localSobolev_of_lipschitz hfin (LipschitzWith.const c)
  filter_upwards [weakGradient_locality hχ hcS hS hc,weakGradient_const (m := m) c,
    abs_gamma_le hfin hpar hχ hv] with x h1 h2 h3 hx
  apply abs_nonpos_iff.mp
  simpa only [h1 hx,h2,zero_mul] using h3

lemma gamma_zero_of_const_on_support (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ v η : X → ℝ} (hχ : LocalSobolev m χ) (hv : LocalSobolev m v)
    (hη : Measurable η) {c : ℝ} (hc : ∀ x,η x ≠ 0 → χ x=c)
    (hv0 : ∀ x,η x=0 → v x=0) : gamma m χ v =ᵐ[m] 0 := by
  have hS : MeasurableSet (Function.support η) := measurableSet_support hη
  have h1 := gamma_zero_on_const_set hfin hpar hχ hv hS (ae_of_all _ hc)
  have h2 := gamma_zero_off_set hfin hpar hv hχ hS (ae_of_all _ fun x hx => hv0 x (not_not.mp hx))
  filter_upwards [h1,h2,gamma_comm (m := m) χ v] with x ha hb he
  by_cases hx : η x=0
  · rw [he,hb (by simpa only [Function.mem_support,not_not] using hx)]
    rfl
  · exact ha hx

lemma IsTestFunction.laplacian_mul_eq_zero_on_plateau
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ η : X → ℝ} (hχ : IsTestFunction m χ) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) {c : ℝ} (hc : ∀ x,η x ≠ 0 → χ x=c) :
    (fun x => laplacian m χ x*η x) =ᵐ[m] 0 := by
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hηB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hηD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  let A := laplacian m χ
  have hu : Sobolev m (fun x => A x*(η x*η x)) :=
    hχ.2.2.2.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hηB hηD
  have hz : gamma m χ (fun x => A x*(η x*η x)) =ᵐ[m] 0 :=
    gamma_zero_of_const_on_support hfin hpar (laplacian_isLaplacian hχ.1).1.2.1 hu.2.1 hη.continuous.measurable hc
      (fun x hx => by rw [hx]; ring)
  have HH := (laplacian_isLaplacian hχ.1).2.2 (fun x => A x*(η x*η x)) hu
  rw [integral_congr_ae hz] at HH
  simp only [Pi.zero_apply,integral_zero] at HH
  have hAη : MemLp (fun x => A x*η x) 2 m :=
    memLp_mul_bounded (laplacian_isLaplacian hχ.1).2.1 hη.continuous.aestronglyMeasurable (ae_of_all _ hη1)
  have he : (∫ x,(A x*η x)^2 ∂m) = 0 := by
    have HH' : (∫ x,A x*(A x*(η x*η x)) ∂m) = 0 := by linarith only [HH]
    convert HH' using 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (A x*η x)) (hAη.integrable_sq)).mp he
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx
end WeakHessian

end
end InlinedFile165

end OAI
