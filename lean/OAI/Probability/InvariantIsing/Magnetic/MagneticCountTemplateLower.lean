import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteTemplateLower
import OAI.Probability.InvariantIsing.Fields.PositiveFieldApproximation

namespace OAI

/-! Spectral and field rational populations with different denominators
have a common physical block template. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_count_template_pressure_lower
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
    (w : A → ℕ) (hd : 0 < ∑ a, w a)
    (γ : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ a, (w a : ℝ)=(∑ a, w a : ℕ)*γ a)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  let d := ∑ a, w a
  have htot : ∑ a, n*w a=n*d := by rw [← Finset.mul_sum]
  let group := countedFieldGroup (fun a => n*w a) htot
  have hgroup a : (spinGroupSize group a : ℝ)=(n*d : ℕ)*γ a := by
    rw [countedFieldGroup_size,Nat.cast_mul,hcount,Nat.cast_mul]
    ring
  have hspec' : ∑ a, d*spec a=n*d := by rw [← Finset.mul_sum,hspec,Nat.mul_comm]
  have hρspec' a : (d*spec a : ℕ)=(n*d : ℕ)*ρ a := by
    rw [Nat.cast_mul,hρspec,Nat.cast_mul]
    ring
  exact finite_template_magnetic_pressure_lower hhaar hgauss hpub hm (Nat.mul_pos hn hd)
    ρ lam hρ hsum hK hlam amax hmax μ (fun a => d*spec a)
    (fun a => Nat.mul_pos hd (hsp a)) hspec' hρspec' e he group γ hγ hγsum hgroup
    g b hg hD hb

end InvariantIsing

end

end OAI
