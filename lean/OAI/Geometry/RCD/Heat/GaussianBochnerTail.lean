import OAI.Geometry.RCD.Heat.GaussianBochnerShell
import OAI.Geometry.RCD.Heat.SummableShellTail

namespace OAI

/-! # Uniform Gaussian tails under quantitative local Bochner bounds -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [ProperSpace X]

theorem gaussian_bochner_uniform_tail (p : X)
    {M V A B D Q₀ Q₁ ℓ : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁)
    (hvol : ∀ r : ℝ, 1 ≤ r → μ.real (closedBall p (2*r)) ≤ V*Real.exp (A*r))
    (ρ F : Y → X → ℝ) (hF : ∀ y, Integrable (F y) μ)
    (hρD : ∀ y x, ρ y x ≤ D)
    (hρtail : ∀ y x, ℓ ≤ dist x p → ρ y x ≤ B*Real.exp (-(dist x p)^2/40))
    (hlocal : ∀ r : ℝ, 0 < r → ∃ (σ : Measure X) (_ : IsFiniteMeasure σ),
      σ.real (closedBall p r) ≤ M*Real.sqrt ((1+r⁻¹^2)*μ.real (closedBall p (2*r))) ∧
      ∀ y, ∀ᵐ x ∂μ.restrict (closedBall p r),
        |F y x| ≤ ρ y x*(Q₀+Q₁*(dist x p)^2)*(1+(σ.rnDeriv μ x).toReal)) :
    ∃ L : ℝ, 1 ≤ L ∧ TendstoUniformly
      (fun N y => ∫ x in (ball p (2^N*L))ᶜ, |F y x| ∂μ) (fun _ => 0) atTop := by
  let L := max 1 ℓ
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  let C := max D B*(Q₀+Q₁)*(V+M*(1+2*V))*L^2
  let E j := C*(4:ℝ)^j*Real.exp (A*L*2^j)*gaussianShellFactor (L^2/40) j
  have hsum : Summable E := by
    have hh := (summable_shell_with_linear_growth (b := 4) (c := L^2/40)
      (by norm_num) (by positivity) (A*L)).mul_left C
    simpa only [E,mul_assoc] using hh
  refine ⟨L,hL,?_⟩
  apply uniform_dyadic_integral_tails μ p hL0 (fun y x => |F y x|)
    (fun y => (hF y).abs) (fun _ => Eventually.of_forall fun _ => abs_nonneg _) (A := E) _ hsum
  intro y j
  have hr : 0 < (2:ℝ)^j*L := mul_pos (by positivity) hL0
  obtain ⟨σ,hσ,hm,hpoint⟩ := hlocal _ hr
  let := hσ
  exact gaussian_bochner_shell_bound μ p hM hA hB hD hQ₀ hQ₁ hL (le_max_right _ _)
    hvol (ρ y) (F y) (hρD y) (hρtail y) j σ hm (hF y).aestronglyMeasurable (hpoint y)

end RegularPointCoordinates

end

end OAI
