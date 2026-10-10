import OAI.Probability.InvariantIsing.Fields.FieldTiltedPairDerivative
import OAI.Probability.InvariantIsing.Fields.FieldGaussianQuadraticEnvelope

namespace OAI

/-! Polynomial envelopes for differentiating the finite scalar Gaussian
recursion twice. The envelope has degree two in the single Gaussian mark. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_mark_one_add_le_sq (u : ℝ) : 1 + |u| ≤ (1 + |u|) ^ 2 := by
  nlinarith [abs_nonneg u]

lemma field_gaussianPair_hasFDerivAt
    (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p) (hpS : p ∈ S)
    (ζ C L CA CD CE : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (_hCE : 0 ≤ CE)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) (gaussianReal 0 1))
    (hDA : AEStronglyMeasurable (DA p) (gaussianReal 0 1))
    (hExp : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ Real.exp (C + L * |u|))
    (hAb : ∀ q ∈ S, ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hDb : ∀ q ∈ S, ∀ u, ‖DU q u‖ ≤ CD * (1 + |u|))
    (hEb : ∀ q ∈ S, ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u
      ∂(gaussianReal 0 1).tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u))) p := by
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|) * (1 + |u|) ^ 2
  have hEi : Integrable E (gaussianReal 0 1) :=
    field_gaussian_quadratic_envelope_integrable C L
  have hE : Integrable (fun u => Real.exp (ζ * U p u)) (gaussianReal 0 1) := by
    apply hEi.mono' ((hU p).const_mul ζ).exp.aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hExp p hpS u).trans (le_mul_of_one_le_right (Real.exp_pos _).le (by
      nlinarith [abs_nonneg u]))
  have hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u)
      (gaussianReal 0 1) := by
    apply (hEi.const_mul CA).mono' (((hU p).const_mul ζ).exp.mul (hA p)).aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    change ‖Real.exp (ζ * U p u) * A p u‖ ≤ CA * E u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|)) :=
        mul_le_mul (hExp p hpS u) (hAb p hpS u) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hCA) (Real.exp_pos _).le
      _ = CA * E u := by dsimp only [E]; ring
  apply field_tiltedFamily_covariance_hasFDerivAt (gaussianReal 0 1) U A DU DA
    hS ζ hU hA hDU hDA hE hEA
    (fun u => (|ζ| * CD) * E u) (fun u => (CE + |ζ| * CA * CD) * E u)
    (hEi.const_mul _) (hEi.const_mul _)
  · intro q hq u
    rw [fieldWeightDifferential, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|))) :=
        mul_le_mul (hExp q hq u)
          (mul_le_mul_of_nonneg_left (hDb q hq u) (abs_nonneg _))
          (by positivity) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|) ^ 2)) := by
        gcongr
        exact field_mark_one_add_le_sq u
      _ = _ := by dsimp only [E]; ring
  · intro q hq u
    rw [fieldObservableDifferential, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hinner : ‖DA q u + (ζ * A q u) • DU q u‖ ≤
        (CE + |ζ| * CA * CD) * (1 + |u|) ^ 2 := by
      calc
        _ ≤ ‖DA q u‖ + ‖(ζ * A q u) • DU q u‖ := norm_add_le _ _
        _ = ‖DA q u‖ + |ζ| * |A q u| * ‖DU q u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ CE * (1 + |u|) ^ 2 + |ζ| * (CA * (1 + |u|)) * (CD * (1 + |u|)) := by
          gcongr
          · exact hEb q hq u
          · exact hAb q hq u
          · exact hDb q hq u
        _ = _ := by ring
    calc
      _ ≤ Real.exp (C + L * |u|) * ((CE + |ζ| * CA * CD) * (1 + |u|) ^ 2) :=
        mul_le_mul (hExp q hq u) hinner (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [E]; ring
  · exact dU
  · exact dA

end InvariantIsing

end

end OAI
