import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Geometry.NodalSets.Elliptic.BasisDivergence

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m : Type*} [Fintype n] [Fintype m]

lemma separated_factor_horizontal_derivative (a : E → ℝ) (k : F → ℝ)
    {x : E} {t : F} (ha : DifferentiableAt ℝ a x) (hk : DifferentiableAt ℝ k t) (v : E) :
    fderiv ℝ (fun y : E × F ↦ k y.2 * a y.1) (x,t) (v,0) =
      k t * fderiv ℝ a x v := by
  have ha' : DifferentiableAt ℝ (fun y : E × F ↦ a y.1) (x,t) :=
    ha.comp (x,t) differentiableAt_fst
  have hk' : DifferentiableAt ℝ (fun y : E × F ↦ k y.2) (x,t) :=
    hk.comp (x,t) differentiableAt_snd
  rw [show (fun y : E × F ↦ k y.2 * a y.1) =
    (fun y : E × F ↦ k y.2) * (fun y : E × F ↦ a y.1) by rfl, fderiv_mul hk' ha']
  have hd1 : fderiv ℝ (fun y : E × F ↦ a y.1) (x,t) =
      (fderiv ℝ a x).comp (ContinuousLinearMap.fst ℝ E F) := by
    rw [show (fun y : E × F ↦ a y.1) = a ∘ Prod.fst from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.fst) (g := a) (x,t) ha differentiableAt_fst using 1
    simp only [fderiv_fst]
  have hd2 : fderiv ℝ (fun y : E × F ↦ k y.2) (x,t) =
      (fderiv ℝ k t).comp (ContinuousLinearMap.snd ℝ E F) := by
    rw [show (fun y : E × F ↦ k y.2) = k ∘ Prod.snd from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.snd) (g := k) (x,t) hk differentiableAt_snd using 1
    simp only [fderiv_snd]
  rw [hd1,hd2]
  simp

lemma separated_factor_divergence (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) :
    ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = k t * ∑ i, fderiv ℝ (a i) x (b i) := by
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have hb (i : n) : (b.prod c) (Sum.inl i) = (b i,0) := by
    ext <;> simp
  simp_rw [hb]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,Finset.sum_const_zero,add_zero]
  simp_rw [separated_factor_horizontal_derivative _ k (ha _) hk]
  rw [Finset.mul_sum]

lemma separated_density_cancellation (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) (d : ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) (hkp : k t ≠ 0) :
    (d*k t)⁻¹ * ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = d⁻¹ * ∑ i, fderiv ℝ (a i) x (b i) := by
  rw [separated_factor_divergence b c a k ha hk,_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
