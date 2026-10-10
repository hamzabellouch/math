import Mathlib
import OAI.Geometry.WeakHessian.Transport.FormAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma logarithmic_shift_error_absorb
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) {R : Lp ℝ 2 m → ℝ}
    (hv : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪v,f⟫_ℝ ≤ A+(∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m)+R f)
    (t : ℝ) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ}
    (hR : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      R (f+t•r) ≤ E+t^2*(∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m)) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    2*⟪v+t•L,f⟫_ℝ ≤ A+E-2*t*⟪v+t•L,r⟫_ℝ+
      ∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m := by
  dsimp only
  let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
  have hre : (r : X → ℝ) =ᵐ[m] regularizedLog ε ∘ (u : X → ℝ) :=
    (regularizedLog_memLp hε u).coeFn_toLp
  have hr : Sobolev m (r : X → ℝ) := (sobolev_congr_ae hre).mpr
    (hu.1.comp_contDiff_lipschitz hfin (regularizedLog_contDiff hε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε))
  have hρm : AEStronglyMeasurable (fun x => u x+ε) m :=
    (Lp.memLp u).aestronglyMeasurable.add_const ε
  have hρb : ∀ᵐ x ∂m, |u x+ε| ≤ B+ε := by
    filter_upwards [hub] with x hx
    exact (abs_add_le _ _).trans (by rw [abs_of_pos hε]; linarith)
  have hcross (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      (∫ x, (u x+ε)*gamma m f r x ∂m) = -⟪L,f⟫_ℝ := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, gamma m f u x ∂m := by
        apply integral_congr_ae
        filter_upwards [gamma_congr_ae (Filter.EventuallyEq.rfl : (f : X → ℝ) =ᵐ[m] f) hre,
          regularizedLog_weighted_gamma hfin hpar hu.1 hf hun hε] with x h1 h2
        rw [h1]; exact h2
      _ = ∫ x, gamma m u f x ∂m := integral_congr_ae (gamma_comm _ _)
      _ = _ := by
        rw [hu.2.2 f hf]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [RCLike.inner_apply,conj_trivial]; ring
  have hrq : (∫ x, (u x+ε)*(weakGradient m r x)^2 ∂m) = -⟪L,r⟫_ℝ := by
    rw [← hcross r hr]
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) (r : X → ℝ)] with x hx
    rw [hx]
  have hfr : Sobolev m (f+t•r : Lp ℝ 2 m) := by
    apply (sobolev_congr_ae ?_).mpr (hf.add hfin (hr.const_mul t))
    filter_upwards [Lp.coeFn_add f (t•r),Lp.coeFn_smul t r] with x ha hs
    simp only [ha,hs,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have H := hv (f+t•r) hfr
  have HR := hR
  change R (f+t•r) ≤ E+t^2*(∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m) at HR
  rw [hrq] at HR
  rw [weighted_gradient_add_smul hfin hpar hf hr hρm hρb t,hcross f hf,hrq] at H
  simp only [inner_add_right,inner_smul_right,inner_add_left,real_inner_smul_left] at H ⊢
  nlinarith

lemma logarithmic_shift_split_absorb
    (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u L v : Lp ℝ 2 m} (hu : IsLaplacian m u L)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    {ε A : ℝ} (hε : 0 < ε) {R : Lp ℝ 2 m → ℝ}
    (hv : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      2*⟪v,f⟫_ℝ ≤ A+(∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m)+R f)
    (t : ℝ) {f : Lp ℝ 2 m} (hf : Sobolev m (f : X → ℝ)) {E : ℝ}
    (hRf : R f ≤ E)
    (hsplit : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      R (f+t•r) ≤ 2*R f+2*t^2*R r)
    (hrelative : let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
      2*R r ≤ ∫ x,(u x+ε)*(weakGradient m r x)^2 ∂m) :
    let r := (regularizedLog_memLp hε u).toLp (fun x => regularizedLog ε (u x))
    2*⟪v+t•L,f⟫_ℝ ≤ A+2*E-2*t*⟪v+t•L,r⟫_ℝ+
      ∫ x,(u x+ε)*(weakGradient m f x)^2 ∂m := by
  apply logarithmic_shift_error_absorb hfin hpar hu hun hub hε hv t hf
  dsimp only at hsplit hrelative ⊢
  nlinarith [mul_le_mul_of_nonneg_left hrelative (sq_nonneg t)]

end WeakHessian

end
end

end OAI
