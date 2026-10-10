import OAI.Probability.InvariantIsing.Haar.HaarHeatEntropy

namespace OAI

/-! Integrated logarithmic-gradient control for a positive heat orbit. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
namespace InvariantIsing

theorem haarHeat_fisher_bound {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d)
    (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ U, haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ) ≤
      C*Real.exp (-2*((N:ℝ)-2)*t)*(∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ) := by
  let q : MatrixPolynomial N := (haarPolynomialHeat N d t p : haarPolynomialSpace N d)
  let a := C*Real.exp (-2*((N:ℝ)-2)*t)
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hpos (U : SpecialOrthogonal N) : 0 < haarPolynomialValue q U :=
    hε.trans_le ((haarPolynomialHeat_bounds p ε P hp (fun V => (le_abs_self _).trans (hP V)) ht U).1)
  have hiG : Integrable (fun U => haarPolynomialValue (haarPolynomialGamma q q) U/
      haarPolynomialValue q U) μ := continuous_haar_integrable μ _
    ((continuous_haarPolynomialValue _).div (continuous_haarPolynomialValue _) (fun U => (hpos U).ne'))
  have hiu : Integrable (fun U => a*haarPolynomialValue q U) μ :=
    (haarPolynomialValue_integrable q μ).const_mul a
  have hb : (∫ U, haarPolynomialValue (haarPolynomialGamma q q) U/haarPolynomialValue q U ∂μ) ≤
      ∫ U, a*haarPolynomialValue q U ∂μ := by
    apply integral_mono hiG hiu
    intro U
    apply (div_le_iff₀ (hpos U)).mpr
    have hh := haarPolynomialHeat_log_gradient_bound p ε C hε hp hC ht U
    change haarPolynomialValue (haarPolynomialGamma q q) U ≤ a*(haarPolynomialValue q U)^2 at hh
    nlinarith [hh]
  rw [integral_const_mul,haarPolynomialHeat_mean] at hb
  exact hb

end InvariantIsing

end

end OAI
