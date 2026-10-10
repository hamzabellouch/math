import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteTemplateLower
import OAI.Probability.InvariantIsing.Magnetic.MagneticPhysicalFieldUpper

namespace OAI

/-! Conditional full-sequence pressure convergence for a finite spectral
and external-field template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_template_magnetic_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (spec : Fin m → ℕ) (hsp : ∀ a, 0 < spec a) (hspec : ∑ a, spec a=n)
    (hρspec : ∀ a, (spec a : ℝ)=(n : ℝ)*ρ a)
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ) (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : Tendsto (fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M) atTop
      (𝓝 (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal) := by
  have hlo := finite_template_magnetic_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec e he group γ
    (fun a => (hγ a).le) hγsum hcount g b hg hD hb
  have hup := finite_physical_field_pressure_upper hhaar hgauss ρ lam hρ hsum μ e he
    g γ b hγ hγsum hg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlo (ε/2) (half_pos hε),hup (ε/2) (half_pos hε)] with M hl hu
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
