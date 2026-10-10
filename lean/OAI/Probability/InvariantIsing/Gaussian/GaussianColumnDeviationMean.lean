import OAI.Probability.InvariantIsing.Gaussian.GaussianColumnDeviation

namespace OAI

/-! Conditional Gaussian quadratic fluctuation, averaged over the actual remaining columns. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

lemma gaussianGramColumnDeviation_insert_integral {N m : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (j : Fin (m+1)) (g : Fin m → Fin N → ℝ) :
    (∫ x : Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray (j.insertNth x g)) j
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) ≤ Real.sqrt (2/((N : ℝ)*t^2)) := by
  let B := gaussianGramLeaveOneOut (gaussianColumnArray (j.insertNth 0 g)) j
  have hB : B.PosSemidef := gaussianGramLeaveOneOut_posSemidef _ j
  have he (x : Fin N → ℝ) :
      gaussianGramColumnDeviation t (gaussianColumnArray (j.insertNth x g)) j =
      |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) (WithLp.toLp 2 x)-
        (positiveResolvent t B).trace/N| := by
    unfold gaussianGramColumnDeviation
    rw [gaussianGramColumnQuadratic_eq]
    simp only [Fin.insertNth_apply_same,gaussianGramLeaveResolvent,
      gaussianGramLeaveOneOut_insertNth j x 0 g,positiveResolvent,B]
  simp_rw [he]
  have hz : HasLaw (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      (stdGaussian _) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have htrans : (∫ x : Fin N → ℝ, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B)
      (WithLp.toLp 2 x)-(positiveResolvent t B).trace/N| ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
        (positiveResolvent t B).trace/N| ∂stdGaussian _ := by
    simpa only [Function.comp_def] using (hz.integral_comp
        (f := fun x => |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
          (positiveResolvent t B).trace/N|)
        (((gaussianQuadraticForm_continuous _).const_mul _).sub continuous_const).abs.aestronglyMeasurable)
  rw [htrans]
  exact positiveResolvent_normalized_fluctuation hN ht hB

theorem gaussianGramColumnDeviation_mean_le {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (j : Fin (m+1)) :
    (∫ g : Fin (m+1) → Fin N → ℝ, gaussianGramColumnDeviation t (gaussianColumnArray g) j
      ∂Measure.pi (fun _ : Fin (m+1) => Measure.pi (fun _ : Fin N => gaussianReal 0 1))) ≤
      Real.sqrt (2/((N : ℝ)*t^2)) := by
  let μ := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin (m+1) => μ)
  let ρ := Measure.pi (fun _ : Fin m => μ)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Fin N → ℝ) j).symm
  let F := fun g : Fin (m+1) → Fin N → ℝ => gaussianGramColumnDeviation t (gaussianColumnArray g) j
  have hm : MeasurePreserving e (μ.prod ρ) ν := (measurePreserving_piFinSuccAbove (fun _ => μ) j).symm
  have hi : Integrable F ν := gaussianGramColumnDeviation_integrable hN ht j
  have hip : Integrable (F ∘ e) (μ.prod ρ) := hm.hasLaw.integrable_comp hi
  calc
    _ = ∫ p, F (e p) ∂μ.prod ρ := (hm.integral_comp' F).symm
    _ = ∫ g, ∫ x, F (e (x,g)) ∂μ ∂ρ := integral_prod_symm _ hip
    _ ≤ ∫ _ : Fin m → Fin N → ℝ, Real.sqrt (2/((N : ℝ)*t^2)) ∂ρ := by
      apply integral_mono hip.integral_prod_right (integrable_const _)
      intro g
      exact gaussianGramColumnDeviation_insert_integral hN ht j g
    _ = _ := by simp

end InvariantIsing

end

end OAI
