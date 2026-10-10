import OAI.MeasureTheory.Falconer.Geometry.ChartGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-!
# Uniform derivatives of the normalized line chart

The scalar denominator is a smooth function of two real variables on a
fixed compact square. Its bounds are independent of the chart center,
tangent direction, and displacement. No analytic input is assumed here.
-/

namespace Falconer
open Set
open scoped ContDiff

private noncomputable def partialSecond (F : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => F
  | n+1 => fun p => fderiv ℝ (partialSecond F n) p (0,1)

private theorem partialSecond_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (partialSecond F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem partialSecond_eq {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (s u : ℝ) :
    partialSecond F n (s,u) = iteratedDeriv n (fun x => F (s,x)) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have hp : HasDerivAt (fun x : ℝ => (s,x)) (0,1) u :=
      (hasDerivAt_const u s).prodMk (hasDerivAt_id u)
    have hh := ((partialSecond_smooth hF n).differentiable (by simp) (s,u)).hasFDerivAt.comp_hasDerivAt u hp
    rw [iteratedDeriv_succ]
    change fderiv ℝ (partialSecond F n) (s,u) (0,1) = _
    rw [← hh.deriv]
    congr 1
    funext x
    exact ih x

private theorem uniform_section_derivatives {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => F (s,x)) u| ≤ C := by
  have hc := (partialSecond_smooth hF n).continuous.abs
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs u hu
  rw [← partialSecond_eq hF]
  exact (hC ⟨(s,u),⟨hs,hu⟩,rfl⟩).trans (le_max_left _ _)

noncomputable def chartLineKernel (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt (1+p.1^2+p.2^2))⁻¹

theorem chartLineKernel_smooth : ContDiff ℝ ∞ chartLineKernel := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact (h.sqrt (fun p => by positivity)).inv (fun p => by positivity)

theorem chartLineKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives chartLineKernel_smooth n

theorem chartLineLinearKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => x * chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives (contDiff_snd.mul chartLineKernel_smooth) n

noncomputable def chartDensityKernel (d : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1+p.1^2+p.2^2)^(-(d : ℝ)/2)

theorem chartDensityKernel_smooth (d : ℕ) : ContDiff ℝ ∞ (chartDensityKernel d) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact h.rpow_const_of_ne (fun p => by positivity)

theorem chartDensityKernel_derivatives (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartDensityKernel d (s,x)) u| ≤ C :=
  uniform_section_derivatives (chartDensityKernel_smooth d) n

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_norm_sq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    ‖(w+y)+u•t‖^2 = 1+‖y‖^2+u^2 := by
  rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,real_inner_smul_right,
    real_inner_smul_right,hwy,hwt,hyt,hw,norm_smul,ht,Real.norm_eq_abs]
  simp only [one_pow,mul_zero,zero_add,mul_one,sq_abs]
  ring

theorem tangent_line_phase_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (v : E) (u : ℝ) :
    inner ℝ (normalizedLine (w+y) t u) v =
      inner ℝ (w+y) v * chartLineKernel (‖y‖,u) +
        inner ℝ t v * (u * chartLineKernel (‖y‖,u)) := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,real_inner_smul_left,inner_add_left,hn,chartLineKernel]
  ring

theorem tangent_line_phase_smooth {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (v : E) :
    ContDiff ℝ ∞ (fun u => inner ℝ (normalizedLine (w+y) t u) v) := by
  simp_rw [tangent_line_phase_eq hw ht hwy hwt hyt]
  have hk : ContDiff ℝ ∞ (fun u => chartLineKernel (‖y‖,u)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  exact (contDiff_const.mul hk).add (contDiff_const.mul (contDiff_id.mul hk))

/-- All phase derivatives on the unit chart are bounded by the displacement
norm, with constants independent of the ambient dimension and chart. -/
theorem tangent_line_phase_derivatives (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t v : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => inner ℝ (normalizedLine (w+y) t x) v) u| ≤ B*‖v‖ := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives n
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives n
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t v hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x * chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have ha : |inner ℝ (w+y) v| ≤ 2*‖v‖ := by
    apply (abs_real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_add_le _ _).trans (by rw [hw]; linarith)
  have hb : |inner ℝ t v| ≤ ‖v‖ := by
    simpa only [ht,one_mul] using abs_real_inner_le_norm t v
  simp_rw [tangent_line_phase_eq hw ht hwy hwt hyt]
  rw [iteratedDeriv_fun_add (f := fun x => inner ℝ (w+y) v * chartLineKernel (‖y‖,x))
    (g := fun x => inner ℝ t v * (x * chartLineKernel (‖y‖,x)))
    ((contDiff_const.mul hk).of_le (by simp)).contDiffAt
    ((contDiff_const.mul hl).of_le (by simp)).contDiffAt,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  calc
    _ ≤ |inner ℝ (w+y) v * iteratedDeriv n (fun x => chartLineKernel (‖y‖,x)) u| +
        |inner ℝ t v * iteratedDeriv n (fun x => x*chartLineKernel (‖y‖,x)) u| := abs_add_le _ _
    _ = |inner ℝ (w+y) v| * |iteratedDeriv n (fun x => chartLineKernel (‖y‖,x)) u| +
        |inner ℝ t v| * |iteratedDeriv n (fun x => x*chartLineKernel (‖y‖,x)) u| := by rw [abs_mul,abs_mul]
    _ ≤ (2*‖v‖)*C + ‖v‖*D := add_le_add
      (mul_le_mul ha (hCb _ hys _ hu) (abs_nonneg _) (by positivity))
      (mul_le_mul hb (hDb _ hys _ hu) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end InnerProduct

end Falconer

end OAI
