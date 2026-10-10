import OAI.MeasureTheory.Falconer.Shells.HighShellKernelTerms
import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization

namespace OAI

namespace PlanarFalconer
open MeasureTheory
namespace PositiveDistanceData

noncomputable def absorbedInverseCoefficient (d : PositiveDistanceData) (j : ℕ)
    (v : ℝ) (b : ℂ × (PairMaskIndex → ℕ)) : ℂ :=
  b.1 * ((2:ℝ)^(-(j:ℝ)*(v-d.a))*assignmentScale d.inverseDescriptorList d.N d.sig b.2 : ℝ)

noncomputable def normalizedHighShellKernel (d : PositiveDistanceData) (n : ℕ)
    (v r : ℝ) (ψ : UnitCircle → ℂ) (z : Plane × Plane) : ℂ :=
  (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
    ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ) *
      ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
        d.absorbedInverseCoefficient j v b *
          (((((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))⁻¹)^j:ℝ):ℂ) *
            sourceDistanceKernel ψ (d.inverseEndpointSymbol b.2 0)
              (d.inverseEndpointSymbol b.2 1) r z.1 z.2))).sum

 theorem absorbedInverseCoefficient_norm (d : PositiveDistanceData)
    (hsig : 0 ≤ d.sig) (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ))
    (hw : d.a+100*d.q < d.t) {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)) :
    ‖d.absorbedInverseCoefficient j v b‖ ≤ ‖b.1‖ := by
  have he := minimal_assignment_scale_absorbed (fun n => d.mass n-(n:ℝ)/(d.N:ℝ))
    hsig hq hqs hw hv hb
  rw [absorbedInverseCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simp only [inverseDescriptorList]
  rw [abs_of_nonneg he.1]
  exact (mul_le_mul_of_nonneg_left he.2 (norm_nonneg _)).trans_eq (mul_one _)

 theorem weightedInverseCircle_normalized (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (n : ℕ) (v : ℝ) {r : ℝ} (hr : 0 < r) {z : Plane × Plane} (hz : 0 < dist z.1 z.2)
    (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) :
    (((dist z.1 z.2/(2:ℝ)^(-(d.a:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
      sourceInverseCircleIntegral n r (z.1-z.2) ψ (d.pairMaskSymbol z) =
      d.normalizedHighShellKernel n v r ψ z := by
  rw [d.inverseCircleIntegral_kernel_terms hQ n ψ hψ hP hp r z,
    ← mul_assoc, ← Complex.ofReal_mul,
    high_shell_weight_cancellation hr hz (by positivity)]
  unfold normalizedHighShellKernel
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.ofReal_pow, high_shell_inverse_power_split]
  simp only [Complex.ofReal_mul, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [absorbedInverseCoefficient, Complex.ofReal_mul]
  ring

end PositiveDistanceData

end PlanarFalconer

end OAI
