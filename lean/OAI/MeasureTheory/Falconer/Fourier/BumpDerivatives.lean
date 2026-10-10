import OAI.MeasureTheory.Falconer.Fourier.AmbientSymbols
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-!
# Uniform derivatives of scaled cap bumps

A single compactly supported bump controls every center and radius. The
scale enters through the curve supplied to that fixed bump, so the k-th
bound loses only the k-th power of the inverse cap radius.
-/

namespace Falconer
open Set
open scoped ContDiff

private noncomputable def unitCapBump (d : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

theorem capBump_eq_unit {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) (x : Space d) :
    capBump δ hδ c x = unitCapBump d ((δ/2)⁻¹ • (x-(c : Space d))) := by
  have hr : δ/(δ/2) = 2 := by field_simp
  simp only [ContDiffBump.apply,capBump,unitCapBump,hr,div_one,inv_one,one_smul,sub_zero]

/-- This applies to an arbitrary smooth curve and will be specialized to the
rotated normalized line. The constant is independent of its center and scale. -/
theorem capBump_curve_derivatives (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere d) (γ : ℝ → Space d), ContDiff ℝ ∞ γ →
      ∀ (D u : ℝ), 1 ≤ D →
      (∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k γ u‖ ≤ D^k) →
      |iteratedDeriv m (fun t => capBump δ hδ c (γ t)) u| ≤ C*(D/δ)^m := by
  obtain ⟨B,hB,hBb⟩ := (unitCapBump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (unitCapBump d).contDiff m
  refine ⟨(m.factorial : ℝ)*B*2^m,by positivity,?_⟩
  intro δ hδ hδ1 c γ hγ D u hD hγb
  let f : ℝ → Space d := fun t => (δ/2)⁻¹ • (γ t-(c : Space d))
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact (hγ.sub contDiff_const).const_smul _
  have hscale : 1 ≤ (δ/2)⁻¹ := (one_le_inv₀ (half_pos hδ)).mpr (by linarith)
  have hfb (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
      ‖iteratedFDeriv ℝ k f u‖ ≤ ((δ/2)⁻¹*D)^k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv k (fun t => (δ/2)⁻¹ • (γ t-(c : Space d))) u‖ ≤ _
    rw [iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_fun_sub ((hγ.of_le (by simp)).contDiffAt) contDiffAt_const,
      iteratedDeriv_const,ite_eq_right (by omega : k ≠ 0),sub_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (half_pos hδ))]
    calc
      _ ≤ (δ/2)⁻¹*D^k := mul_le_mul_of_nonneg_left (hγb k hk hkm) (by positivity)
      _ ≤ ((δ/2)⁻¹)^k*D^k := mul_le_mul_of_nonneg_right
        (le_self_pow₀ hscale (by omega)) (pow_nonneg (by linarith) _)
      _ = _ := (mul_pow _ _ _).symm
  have hh := norm_iteratedFDeriv_comp_le (unitCapBump d).contDiff hf
    (show (m : ℕ∞ω) ≤ ∞ by simp) u (fun k hk => hBb k hk _) hfb
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  have he : (unitCapBump d) ∘ f = (fun t => capBump δ hδ c (γ t)) := by
    funext t
    exact (capBump_eq_unit δ hδ c (γ t)).symm
  rw [he,Real.norm_eq_abs] at hh
  apply hh.trans_eq
  have hr : (δ/2)⁻¹*D = 2*(D/δ) := by field_simp
  rw [hr,mul_pow]
  ring

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    normalizedLine (w+y) t u =
      chartLineKernel (‖y‖,u) • (w+y) + (u*chartLineKernel (‖y‖,u)) • t := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,hn,chartLineKernel,smul_add,smul_smul]
  rw [mul_comm]

theorem tangent_line_derivatives (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (normalizedLine (w+y) t) u‖ ≤ B := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives m
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives m
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x*chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have hwyb : ‖w+y‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hw]; linarith)
  have he : normalizedLine (w+y) t = (fun x =>
      chartLineKernel (‖y‖,x) • (w+y) + (x*chartLineKernel (‖y‖,x)) • t) :=
    funext (tangent_line_eq hw ht hwy hwt hyt)
  have hk' : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x) • (w+y)) :=
    hk.smul contDiff_const
  have hl' : ContDiff ℝ ∞ (fun x => (x*chartLineKernel (‖y‖,x)) • t) :=
    hl.smul contDiff_const
  rw [he,iteratedDeriv_fun_add
    ((hk'.of_le (by simp)).contDiffAt) ((hl'.of_le (by simp)).contDiffAt),
    iteratedDeriv_smul_const ((hk.of_le (by simp)).contDiffAt),
    iteratedDeriv_smul_const ((hl.of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ‖iteratedDeriv m (fun x => chartLineKernel (‖y‖,x)) u • (w+y)‖ +
        ‖iteratedDeriv m (fun x => x*chartLineKernel (‖y‖,x)) u • t‖ := norm_add_le _ _
    _ ≤ C*2+D*1 := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul (hCb _ hys _ hu) hwyb (norm_nonneg _) hC)
        (mul_le_mul (hDb _ hys _ hu) ht.le (norm_nonneg _) hD)
    _ = _ := by ring

/-- One fixed scale controls all positive orders up to a chosen finite order. -/
theorem tangent_line_derivative_scale (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (normalizedLine (w+y) t) u‖ ≤ D^k := by
  choose B hB hBb using (fun k => tangent_line_derivatives (E := E) k)
  let D := 1+∑ k ∈ Finset.range (m+1), B k
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (m+1)) => hB k)]
  refine ⟨D,hD,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu k hk hkm
  apply (hBb k w y t hw ht hwy hwt hyt hy u hu).trans
  have hb : B k ≤ D := by
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m+1)) => hB j)
      (Finset.mem_range.mpr (by omega : k < m+1))
    dsimp [D]
    linarith
  exact hb.trans (le_self_pow₀ hD (by omega))

end InnerProduct
end Falconer

end OAI
