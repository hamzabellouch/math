import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ActualRadialCorrugationStrict

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma coordinateCovariantSecond_add_const (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (y : E → V) (d : V) (x : E) :
    coordinateCovariantSecond Γ (fun z => y z+d) x = coordinateCovariantSecond Γ y x := by
  have hh : fderiv ℝ (fun z => y z+d) = fderiv ℝ y := funext fun _ => fderiv_add_const d
  simp only [coordinateCovariantSecond, hh]

omit [FiniteDimensional ℝ E] in
theorem corrugationSecondRemainder_uniform_shift
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ d₀ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F (fun z => y z+d₀) d N x‖ ≤
        C * ((|χ x| + ‖fderiv ℝ χ x‖) * ‖fderiv ℝ F (N • (y x+d₀))‖ + N⁻¹) := by
  obtain ⟨Y₂, hY₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ y)
    (continuous_coordinateCovariantSecond Γ hΓ hy).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y)
    (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨χ₂, hχ₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ χ)
    (continuous_coordinateCovariantSecond Γ hΓ hχ).continuousOn
  let c₁ := |d| * |Y₂|
  let c₂ := 2 * |d| * |Y₁|
  let c₃ := |d| * |B| * |χ₂|
  let C := 1 + c₁ + c₂ + c₃
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hc₁C : c₁ ≤ C := by dsimp [C]; linarith
  have hc₂C : c₂ ≤ C := by dsimp [C]; linarith
  have hc₃C : c₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN d₀ x hx
  have hY₂x := (hY₂ x hx).trans (le_abs_self Y₂)
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hχ₂x := (hχ₂ x hx).trans (le_abs_self χ₂)
  have hBx := (hB (N • (y x+d₀))).trans (le_abs_self B)
  calc
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖ * ‖coordinateCovariantSecond Γ y x‖ +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖ * ‖fderiv ℝ y x‖ +
        |d / N| * |F (N • (y x+d₀))| * ‖coordinateCovariantSecond Γ χ x‖ :=
      by
      simpa only [fderiv_add_const,coordinateCovariantSecond_add_const] using
        corrugationSecondRemainder_norm_bound Γ hψ hχ hF (hy.add (contDiff_const (c:=d₀))) d N (ne_of_gt hN) x
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖ * |Y₂| +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖ * |Y₁| +
        |d / N| * |B| * |χ₂| := by gcongr
    _ = c₁ * (|χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖) +
        c₂ * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖) + c₃ * N⁻¹ := by
      rw [abs_div, abs_of_pos hN]
      dsimp [c₁, c₂, c₃]
      ring
    _ ≤ C * (|χ x| * ‖fderiv ℝ F (N • (y x+d₀))‖) +
        C * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • (y x+d₀))‖) + C * N⁻¹ := by gcongr
    _ = _ := by ring

theorem corrugationSecondRemainder_small_product_scaled_shift
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχn : ∀ x, 0 ≤ χ x)
    (f : V → ℝ) (M Jf : ℝ) (hJf : 0 ≤ Jf)
    (hfn : ∀ z, 0 ≤ f z) (hfM : ∀ z, f z ≤ M)
    (hDf : ∀ z, ‖fderiv ℝ F z‖ ≤ Jf*f z)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ d₀ : V, ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F (fun z => y z+d₀) d N x‖ ≤
        C * (χ x*f (N • (y x+d₀))+Real.sqrt (χ x*f (N • (y x+d₀)))+N⁻¹) := by
  obtain ⟨C₀,hC₀,hrem⟩ := corrugationSecondRemainder_uniform_shift Γ hΓ hψ hχ hF hy K hK d B hB
  obtain ⟨J,hJ,hcut⟩ := exists_cutoff_sqrt_gradient hχ hχs hχn
  let c := J*Real.sqrt M
  have hc : 0 ≤ c := mul_nonneg hJ.le (Real.sqrt_nonneg _)
  refine ⟨C₀*(1+Jf)*(1+c),by positivity,?_⟩
  intro N hN d₀ x hx
  have ht : 0 ≤ χ x*f (N • (y x+d₀)) := mul_nonneg (hχn x) (hfn _)
  have hs := Real.sqrt_nonneg (χ x*f (N • (y x+d₀)))
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hprod : (χ x+‖fderiv ℝ χ x‖)*f (N • (y x+d₀)) ≤
      χ x*f (N • (y x+d₀))+c*Real.sqrt (χ x*f (N • (y x+d₀))) :=
    cutoff_small_product_bound _ _ _ _ _ (hχn x) (norm_nonneg _) (hfn _) (hfM _) hJ.le (hcut x)
  calc
    _ ≤ C₀*((|χ x|+‖fderiv ℝ χ x‖)*‖fderiv ℝ F (N • (y x+d₀))‖+N⁻¹) := hrem N hN d₀ x hx
    _ ≤ C₀*((χ x+‖fderiv ℝ χ x‖)*(Jf*f (N • (y x+d₀)))+N⁻¹) := by
      rw [abs_of_nonneg (hχn x)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (hDf _)
          (add_nonneg (hχn x) (norm_nonneg _))) le_rfl) hC₀.le
    _ = C₀*(Jf*((χ x+‖fderiv ℝ χ x‖)*f (N • (y x+d₀)))+N⁻¹) := by ring
    _ ≤ C₀*(Jf*(χ x*f (N • (y x+d₀))+c*Real.sqrt (χ x*f (N • (y x+d₀))))+N⁻¹) := by gcongr
    _ ≤ C₀*((1+Jf)*(1+c)*(χ x*f (N • (y x+d₀))+Real.sqrt (χ x*f (N • (y x+d₀)))+N⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      have h1 := mul_nonneg hJf ht
      have h2 := mul_nonneg hc ht
      have h3 := mul_nonneg hJf hs
      have h4 := mul_nonneg hJf hNi
      have h5 := mul_nonneg hc hNi
      have h6 := mul_nonneg (mul_nonneg hJf hc) ht
      have h7 := mul_nonneg (mul_nonneg hJf hc) hNi
      have h8 := mul_nonneg hc hs
      nlinarith only [ht,hs,h1,h2,h3,h4,h5,h6,h7,h8]
    _ = _ := by ring

end
end YauCounterexamples

end OAI
