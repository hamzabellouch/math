import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalFubini
import OAI.MeasureTheory.Falconer.Radial.RadialDistanceError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem finite_complex_norm_square {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ((‖∑ i ∈ S, f i‖^2 : ℝ) : ℂ) = ∑ i ∈ S, ∑ j ∈ S, f i * conj (f j) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem angular_integral_cross (f g : UnitCircle → ℂ) (c : ℝ) :
    (∫ u, ∫ w, c • (f u * conj (g w)) ∂sourceArcLength ∂sourceArcLength) =
      c • ((∫ u, f u ∂sourceArcLength) * conj (∫ w, g w ∂sourceArcLength)) := by
  simp_rw [integral_smul, integral_const_mul, integral_conj, integral_mul_const]

theorem bounded_shell_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W)
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ r, ‖f r‖ ≤ C) :
    Integrable (fun r => Ψ (r/R) • f r) := by
  have hb : Integrable (Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C)) :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  apply hb.mono ((hΨ.comp (measurable_id.div_const R)).aestronglyMeasurable.smul hf)
  filter_upwards with r
  by_cases hn : Ψ (r/R) = 0
  · simp [hn]
  · have hh := hs _ hn
    have hr : r ∈ Icc (R/4) (4*R) := by
      constructor
      · have := (lt_div_iff₀ hR).mp hh.1; linarith
      · have := (div_lt_iff₀ hR).mp hh.2; linarith
    change ‖Ψ (r/R) • f r‖ ≤ ‖Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C) r‖
    rw [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW hC),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hw _) (hc r) (norm_nonneg _) hW

theorem finite_angular_square_radial {ι : Type*} (S : Finset ι)
    (f : ι → ℝ × UnitCircle → ℂ) (hf : ∀ i ∈ S, Measurable (f i))
    (C : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hb : ∀ i ∈ S, ∀ p, ‖f i p‖ ≤ C i)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, Ψ (r/R) • ((‖∑ i ∈ S, ∫ u, f i (r,u) ∂sourceArcLength‖^2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ r : ℝ, ∫ u, ∫ w,
        Ψ (r/R) • (f i (r,u) * conj (f j (r,w))) ∂sourceArcLength ∂sourceArcLength := by
  let F := fun i r => ∫ u, f i (r,u) ∂sourceArcLength
  have hFm : ∀ i ∈ S, Measurable (F i) := fun i hi =>
    (hf i hi).stronglyMeasurable.integral_prod_right'.measurable
  have hFb (i : ι) (hi : i ∈ S) (r : ℝ) : ‖F i r‖ ≤ sourceArcLength.real univ * C i :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun u => hb i hi (r,u)))).trans_eq (mul_comm _ _)
  have hcross (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      Integrable (fun r : ℝ => Ψ (r/R) • (F i r * conj (F j r))) := by
    apply bounded_shell_integrable hΨ hs hW hw hR _
      ((hFm i hi).mul (Complex.continuous_conj.measurable.comp (hFm j hj))).aestronglyMeasurable
      (mul_nonneg (mul_nonneg (measureReal_nonneg (μ := sourceArcLength) (s := univ)) (hC i hi))
        (mul_nonneg (measureReal_nonneg (μ := sourceArcLength) (s := univ)) (hC j hj)))
    intro r
    change ‖F i r * conj (F j r)‖ ≤ (sourceArcLength.real univ * C i) * (sourceArcLength.real univ * C j)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hFb i hi r) (hFb j hj r) (norm_nonneg _)
      (mul_nonneg measureReal_nonneg (hC i hi))
  simp_rw [finite_complex_norm_square, Finset.smul_sum, angular_integral_cross]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hcross i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum S (fun j hj => hcross i hi j hj)

end PlanarFalconer

end OAI
