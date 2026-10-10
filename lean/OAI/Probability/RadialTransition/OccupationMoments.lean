import OAI.Probability.RadialTransition.CanonicalDuality

namespace OAI

universe uI uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem exp_weighted_sum_le {I : Type uI} [Fintype I] (w x : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1) :
    Real.exp (∑ i, w i * x i) ≤ 1 - ∑ i, w i + ∑ i, w i * Real.exp (x i) := by
  have hh := convexOn_exp.map_add_sum_le (t := Finset.univ) (w := w) (p := x)
    (v := 1 - ∑ i, w i) (q := 0) (fun i _ => hw i) (by ring)
    (fun _ _ => mem_univ _) (sub_nonneg.mpr hs) (mem_univ _)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] using hh

theorem integral_exp_fraction_le {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => Real.exp (f x)) μ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Integrable (fun x => Real.exp (η * f x)) μ ∧
      (∫ x, Real.exp (η * f x) ∂μ) ≤ Real.exp (η * Real.log (∫ x, Real.exp (f x) ∂μ)) := by
  have hib : Integrable (fun x => Real.exp (η * f x)) μ := by
    apply hi.mono' (Real.measurable_exp.comp (measurable_const.mul hf)).aestronglyMeasurable
    filter_upwards [] with x
    change |Real.exp (η * f x)| ≤ Real.exp (f x)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_left (hf0 x) hη1)
  have hpos : 0 < ∫ x, Real.exp (η * f x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hib).mpr
    simp [Function.support, Real.exp_ne_zero]
  have hpos' : 0 < ∫ x, Real.exp (f x) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi).mpr
    simp [Function.support, Real.exp_ne_zero]
  have hh := log_integral_exp_convex_mix (F := fun _ : X => (0 : ℝ)) (G := f)
    (sub_nonneg.mpr hη1) hη0 (by ring) (by simp) hi
    (by simpa using hib) (by simp) hpos' (by simpa using hpos)
  simp only [mul_zero, zero_add, Real.exp_zero, integral_const, probReal_univ, smul_eq_mul,
    one_mul, Real.log_one] at hh
  refine ⟨hib, ?_⟩
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

theorem occupation_moment_closure {I : Type uI} {X : Type uX} [Fintype I] [Nonempty I]
    [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (f : I → X → ℝ) (θ : I → I → ℝ) {C η : ℝ}
    (hC : 1 ≤ C) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hi : ∀ i, Integrable (fun x => Real.exp (f i x)) μ)
    (hθ : ∀ i j, 0 ≤ θ i j) (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hconditional : ∀ i, (∫ x, Real.exp (f i x) ∂μ) ≤
      C * (∫ x, Real.exp (η * ∑ j, θ i j * f j x) ∂μ)) :
    ∀ i, (∫ x, Real.exp (f i x) ∂μ) ≤ Real.exp (Real.log C / (1 - η)) := by
  classical
  let F (i : I) := ∫ x, Real.exp (f i x) ∂μ
  have hF1 (i : I) : 1 ≤ F i := by
    have hh := integral_mono (integrable_const (1 : ℝ)) (hi i)
      (fun x => Real.one_le_exp_iff.mpr (hf0 i x))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  obtain ⟨k, _, hk⟩ := Finset.univ.exists_max_image F Finset.univ_nonempty
  have hFm (i : I) : F i ≤ F k := hk i (Finset.mem_univ i)
  have hfrac (i : I) := integral_exp_fraction_le (hf i) (hf0 i) (hi i) hη0 hη1.le
  have hless (i : I) : ∫ x, Real.exp (η * ∑ j, θ i j * f j x) ∂μ ≤
      Real.exp (η * Real.log (F k)) := by
    let g : X → ℝ := fun x => 1 - ∑ j, θ i j + ∑ j, θ i j * Real.exp (η * f j x)
    have hig : Integrable g μ :=
      (integrable_const _).add (integrable_finsetSum _ (fun j _ => (hfrac j).1.const_mul _))
    have hpoint (x : X) : Real.exp (η * ∑ j, θ i j * f j x) ≤ g x := by
      have hh := exp_weighted_sum_le (θ i) (fun j => η * f j x) (hθ i) (hrow i)
      dsimp only [g]
      convert hh using 1
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hmix : Integrable (fun x => Real.exp (η * ∑ j, θ i j * f j x)) μ := by
      apply hig.mono' (Real.measurable_exp.comp
        (measurable_const.mul (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hf j))))).aestronglyMeasurable
      filter_upwards [] with x
      change |Real.exp (η * ∑ j, θ i j * f j x)| ≤ g x
      rw [abs_of_pos (Real.exp_pos _)]
      exact hpoint x
    have hh := integral_mono hmix hig hpoint
    have hexp1 : 1 ≤ Real.exp (η * Real.log (F k)) := by
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg hη0 (Real.log_nonneg (hF1 k))
    have hfs (j : I) : ∫ x, Real.exp (η * f j x) ∂μ ≤ Real.exp (η * Real.log (F k)) :=
      (hfrac j).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hF1 j]) (hFm j)) hη0))
    dsimp only [g] at hh
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun j _ => (hfrac j).1.const_mul _)),
      integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_finsetSum _ (fun j _ => (hfrac j).1.const_mul _)] at hh
    simp only [integral_const_mul] at hh
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hfs j) (hθ i j))
    rw [← Finset.sum_mul] at hs
    have := hrow i
    nlinarith
  have hkineq := (hconditional k).trans (mul_le_mul_of_nonneg_left (hless k) (by linarith))
  have hC0 : 0 < C := by linarith
  have hFk0 : 0 < F k := by linarith [hF1 k]
  have hlog := Real.log_le_log hFk0 hkineq
  rw [Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hb : Real.log (F k) ≤ Real.log C / (1 - η) := by
    apply (le_div_iff₀ (sub_pos.mpr hη1)).mpr
    nlinarith
  intro i
  apply (hFm i).trans
  simpa only [Real.exp_log hFk0] using Real.exp_le_exp.mpr hb

end RadialTransition

end

end OAI
