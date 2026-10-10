import OAI.Probability.InvariantIsing.Magnetic.MagneticSpectralPopulationLower
import OAI.Probability.InvariantIsing.Magnetic.MagneticPhysicalFieldUpper

namespace OAI

/-! The full finite-alphabet external-field pressure formula with arbitrary
positive real spectral and field populations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_positive_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m) (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    Tendsto (fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
      (fun i => b (g M i)) ∂μ M) atTop
      (𝓝 (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal) := by
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hlam a : |lam a|≤K := Finset.single_le_sum (f := fun a => |lam a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  obtain ⟨amax,_,hmax⟩ := Finset.exists_max_image Finset.univ lam
    ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  let D := ∑ a, |b a|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb a : |b a|≤D := Finset.single_le_sum (f := fun a => |b a|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hlo := finite_physical_field_pressure_lower hhaar hgauss hpub hm ρ lam hρ hsum
    hK hlam amax (fun a => hmax a (Finset.mem_univ _)) μ e he γ hγ hγsum g b hg hD hb
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
