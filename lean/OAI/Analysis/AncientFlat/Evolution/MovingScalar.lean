import OAI.Analysis.AncientFlat.Kernel.SymbolBounds

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma scalar_space_lipschitz (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ)
    (hL : ∀ x, ‖fderiv ℝ f x‖≤L) (x y : V) :
    ‖f y-f x‖≤L*‖y-x‖ := by
  exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf.differentiable (by decide)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (fun z _ => hL z) (mem_univ x) (mem_univ y)
lemma moving_scalar_deriv (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (x : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (Real.exp (s/4) • x))
      ((1/4:ℝ)*(fderiv ℝ f (Real.exp (t/4) • x)) (Real.exp (t/4) • x)) t := by
  have h := ((hf.differentiable (by decide)).differentiableAt (x := Real.exp (t/4) • x)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).div_const 4).exp.smul_const x)
  convert h using 1 <;> first | rfl | (simp only [id_eq,one_div,ContinuousLinearMap.map_smul,smul_eq_mul]; ring)
lemma moving_scalar_time_lipschitz (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ)
    (hL : ∀ x, ‖x‖*‖fderiv ℝ f x‖≤L) (x : V) (s t : ℝ) :
    ‖f (Real.exp (t/4) • x)-f (Real.exp (s/4) • x)‖≤(L/4)*|t-s| := by
  have hb (r : ℝ) : ‖(1/4:ℝ)*(fderiv ℝ f (Real.exp (r/4) • x)) (Real.exp (r/4) • x)‖≤L/4 := by
    rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/4)]
    calc
      _≤(1/4:ℝ)*(‖fderiv ℝ f (Real.exp (r/4) • x)‖*‖Real.exp (r/4) • x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
      _≤L/4 := by have := hL (Real.exp (r/4) • x); nlinarith
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ => (moving_scalar_deriv f hf x r).hasDerivWithinAt)
      (fun r _ => hb r) (mem_univ s) (mem_univ t)
lemma moving_scalar_space_lipschitz (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ)
    (hL0 : 0≤L) (hL : ∀ x, ‖fderiv ℝ f x‖≤L) (t : ℝ) (ht : t≤1) (x y : V) :
    ‖f (Real.exp (t/4) • y)-f (Real.exp (t/4) • x)‖≤(Real.exp (1/4)*L)*‖y-x‖ := by
  have h := scalar_space_lipschitz f hf L hL (Real.exp (t/4) • x) (Real.exp (t/4) • y)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at h
  refine h.trans ?_
  have he : Real.exp (t/4)≤Real.exp (1/4) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [norm_nonneg (y-x),mul_le_mul_of_nonneg_left he hL0]
end FlatSimilarity

end

end OAI
