import OAI.MeasureTheory.Falconer.Fourier.SymbolOrder
import OAI.MeasureTheory.Falconer.Geometry.AmbientChartBudget
import OAI.MeasureTheory.Falconer.Fourier.ChartSymbolControl

namespace OAI

/-! # Admissible chart bounds for the actual separated endpoint factors

The compact constants are chosen for the whole endpoint family before the
scale parameters. An order-q operator costs exactly D^q in the symbol size.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

namespace SymbolOrder

theorem chartControl {n q : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : Space (n+2) → V → ℂ} {F : Space (n+2) → Space (n+2) → ℂ}
    (h : SymbolOrder B F q) (hF : Measurable (Function.uncurry F)) (K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ x k, k ≤ K+q → ∀ z, ‖iteratedFDeriv ℝ k (B x) z‖ ≤ C*D^k) →
      ChartSymbolControl K (fun x w => F x w) (A*C*D^q) D := by
  choose A hA hAb using fun k => h.bound
    (Metric.sphere (0 : Space (n+2)) 1) (isCompact_sphere _ _) k
  let U := ∑ k ∈ Finset.range (K+1), A k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hA k)
  have hAU (k : ℕ) (hk : k ≤ K) : A k ≤ U :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n K
  have hUH : U ≤ (H+1)*U := by nlinarith
  refine ⟨(H+1)*U,by positivity,?_⟩
  intro C D hC hD hb
  have hscaled (x : Space (n+2)) (k : ℕ) (hk : k ≤ K) (w : Sphere (n+2)) :
      ‖iteratedFDeriv ℝ k (F x) w‖ ≤ (U*C*D^q)*D^k := by
    calc
      _ ≤ A k*C*D^(k+q) := hAb k x C D hC hD
        (fun l hl z => hb x l (by omega) z) w w.property
      _ ≤ U*C*D^(k+q) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hAU k hk) hC) (pow_nonneg (zero_le_one.trans hD) _)
      _ = _ := by rw [pow_add]; ring
  refine ⟨hF.comp (measurable_fst.prodMk (continuous_subtype_val.measurable.comp measurable_snd)),
    ?_,?_,?_⟩
  · intro x w
    have hz := hscaled x 0 (Nat.zero_le _) w
    simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hUH hC) (pow_nonneg (zero_le_one.trans hD) _))
  · intro x e y
    exact (h.smooth x).comp (rotatedChartCurve_contDiff e y)
  · intro e k hk x y hy u hu
    have hh := hHb (F x) (h.smooth x) (U*C*D^q) D
      (by positivity) hD (hscaled x) e y hy u hu k hk
    calc
      _ ≤ H*(U*C*D^q)*D^k := hh
      _ ≤ (H+1)*(U*C*D^q)*D^k := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : H ≤ H+1) (by positivity))
        (pow_nonneg (zero_le_one.trans hD) _)
      _ = _ := by ring

/-- One constant works for every scale label before a label is fixed. -/
theorem chartControlFamily {n q : ℕ} {I V : Type*} [MeasurableSpace I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : I × Space (n+2) → V → ℂ} {F : I × Space (n+2) → Space (n+2) → ℂ}
    (h : SymbolOrder B F q) (hF : Measurable (Function.uncurry F)) (K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (i : I) (C D : ℝ), 0 ≤ C → 1 ≤ D →
      (∀ x k, k ≤ K+q → ∀ z, ‖iteratedFDeriv ℝ k (B (i,x)) z‖ ≤ C*D^k) →
      ChartSymbolControl K (fun x w => F (i,x) w) (A*C*D^q) D := by
  choose A hA hAb using fun k => h.bound
    (Metric.sphere (0 : Space (n+2)) 1) (isCompact_sphere _ _) k
  let U := ∑ k ∈ Finset.range (K+1), A k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hA k)
  have hAU (k : ℕ) (hk : k ≤ K) : A k ≤ U :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n K
  have hUH : U ≤ (H+1)*U := by nlinarith
  refine ⟨(H+1)*U,by positivity,?_⟩
  intro i C D hC hD hb
  have hscaled (x : Space (n+2)) (k : ℕ) (hk : k ≤ K) (w : Sphere (n+2)) :
      ‖iteratedFDeriv ℝ k (F (i,x)) w‖ ≤ (U*C*D^q)*D^k := by
    calc
      _ ≤ A k*C*D^(k+q) := hAb k (i,x) C D hC hD
        (fun l hl z => hb x l (by omega) z) w w.property
      _ ≤ U*C*D^(k+q) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hAU k hk) hC) (pow_nonneg (zero_le_one.trans hD) _)
      _ = _ := by rw [pow_add]; ring
  refine ⟨hF.comp ((measurable_const.prodMk measurable_fst).prodMk
      (continuous_subtype_val.measurable.comp measurable_snd)),
    ?_,?_,?_⟩
  · intro x w
    have hz := hscaled x 0 (Nat.zero_le _) w
    simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hUH hC) (pow_nonneg (zero_le_one.trans hD) _))
  · intro x e y
    exact (h.smooth (i,x)).comp (rotatedChartCurve_contDiff e y)
  · intro e k hk x y hy u hu
    have hh := hHb (F (i,x)) (h.smooth (i,x)) (U*C*D^q) D
      (by positivity) hD (hscaled x) e y hy u hu k hk
    calc
      _ ≤ H*(U*C*D^q)*D^k := hh
      _ ≤ (H+1)*(U*C*D^q)*D^k := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : H ≤ H+1) (by positivity))
        (pow_nonneg (zero_le_one.trans hD) _)
      _ = _ := by ring

end SymbolOrder
end Falconer

end OAI
