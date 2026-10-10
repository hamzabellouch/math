import OAI.Probability.InvariantIsing.Fields.FieldSpinDerivative

namespace OAI

/-! A local integrable envelope permits covariance derivatives of a
Gaussian logarithmic mean without a bounded-payoff assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma hasDerivAt_logMean_of_integrable_envelope
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (F D : ℝ → A → ℝ) (hF : ∀ s, Measurable (F s))
    {ζ t : ℝ} (hζ : ζ ≠ 0) {S : Set ℝ} (hS : S ∈ 𝓝 t)
    (hD : Measurable (D t))
    (hi : Integrable (fun u => Real.exp (ζ * F t u)) μ)
    (hd : ∀ s ∈ S, ∀ u, HasDerivAt (fun q => F q u) (D s u) s)
    (M : A → ℝ) (hM : Integrable M μ)
    (hbound : ∀ᵐ u ∂μ, ∀ s ∈ S, ‖Real.exp (ζ * F s u) * (ζ * D s u)‖ ≤ M u) :
    HasDerivAt (fun s => logMean ζ μ (F s))
      (∫ u, D t u ∂μ.tilted (fun u => ζ * F t u)) t := by
  obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun s => ((hF s).const_mul ζ).exp.aestronglyMeasurable) hi
    (((hF t).const_mul ζ).exp.mul (hD.const_mul ζ)).aestronglyMeasurable
    hbound hM (ae_of_all _ fun u s hs => ((hd s hs u).const_mul ζ).exp)
  have hpos := IsingPerceptron.integral_exp_pos μ (F t) hi
  convert (hI.log hpos.ne').div_const ζ using 1
  · rfl
  · rw [integral_tilted_eq_div]
    have he : (∫ u, Real.exp (ζ * F t u) * (ζ * D t u) ∂μ) =
        ζ * ∫ u, Real.exp (ζ * F t u) * D t u ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    rw [he]
    field_simp

end InvariantIsing

end

end OAI
