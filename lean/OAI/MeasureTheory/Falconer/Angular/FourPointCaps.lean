import OAI.MeasureTheory.Falconer.Radial.RadialPairSwap
import OAI.MeasureTheory.Falconer.Fourier.OscillatoryExpansion

namespace OAI

/-!
# Exact cap expansion of an endpoint cross term

Each cap weight stays inside the original four-point amplitude. The only
factor removed from the integral is the product of the four model-mass
normalizations. The measures are the original restricted endpoint laws.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

noncomputable def capPairAmplitude {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) (x : Space d × Space d) (w : Sphere d) : ℂ :=
  (η w : ℂ) * (b x.1 w * star (b' x.2 w))

noncomputable def endpointCapCrossTerm {d : ℕ}
    (μ μ' ν ν' : Measure (Space d)) (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) : ℂ :=
  ∫ r, ∫ z : Sphere d × Sphere d,
    ((η z.1 : ℂ)*(θ z.2 : ℂ)) *
      ((endpointTransform μ M b r z.1 * endpointTransform ν P c r z.2) *
       star (endpointTransform μ' M' b' r z.1 * endpointTransform ν' P' c' r z.2))
    ∂(sphereMeasure d).prod (sphereMeasure d)
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

theorem endpointCapCrossTerm_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) •
        expandedCapTerm ((μ.prod μ').prod (ν.prod ν')) v Ψ
          (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2)
          (fun x w => capPairAmplitude η b b' x.1 w)
          (fun x w => capPairAmplitude θ c c' x.2 w) := by
  unfold endpointCapCrossTerm expandedCapTerm
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [endpointTransform_four_point]
  rw [mul_smul_comm, ← integral_const_mul, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [capPairAmplitude]
  have he : Complex.I * ((r *
      (inner ℝ (z.1 : Space d) (x.1.1-x.1.2) +
       inner ℝ (z.2 : Space d) (x.2.1-x.2.2)) : ℝ) : ℂ) =
      Complex.I*(r : ℂ)*
        ((inner ℝ (z.1 : Space d) (x.1.1-x.1.2) : ℂ)+
         (inner ℝ (z.2 : Space d) (x.2.1-x.2.2) : ℂ)) := by
    push_cast
    ring
  rw [he]
  apply congrArg (fun z : ℂ => ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) • z)
  ring

theorem capPairAmplitude_measurable {d : ℕ} (η : Sphere d → ℝ)
    (hη : Measurable η) (b b' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b')) :
    Measurable (Function.uncurry (capPairAmplitude η b b')) := by
  unfold capPairAmplitude
  exact (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).mul
    ((hb.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hb'.comp (measurable_fst.snd.prodMk measurable_snd))))

theorem capPairAmplitude_norm_le {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) {H B B' : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hη : ∀ w, |η w| ≤ H) (hb : ∀ x w, ‖b x w‖ ≤ B) (hb' : ∀ x w, ‖b' x w‖ ≤ B')
    (x : Space d × Space d) (w : Sphere d) :
    ‖capPairAmplitude η b b' x w‖ ≤ H*(B*B') := by
  simp only [capPairAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_star]
  exact mul_le_mul (hη w) (mul_le_mul (hb _ _) (hb' _ _) (norm_nonneg _) hB)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hH

end Falconer

end OAI
