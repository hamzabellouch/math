import OAI.Probability.InvariantIsing.Magnetic.MagneticCountTemplateLower
import OAI.Probability.InvariantIsing.Magnetic.MagneticPopulationContinuity
import OAI.Probability.InvariantIsing.Fields.PhysicalFieldPopulationComparison

namespace OAI

/-! Arbitrary positive real field populations are reached from rational
field blocks by quantitative pressure and variational comparisons. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_rational_spectrum_field_pressure_lower
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
    (γ : A → ℝ) (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (g : (M : ℕ) → Fin M → A) (b : A → ℝ)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ))
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ a, |b a| ≤ D)
    : ∀ ε > 0, ∀ᶠ M in atTop,
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M := by
  have hA : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hγsum
  let a0 : A := Classical.choice hA
  let τ := fieldApproxWeights γ
  have hτ := fieldApproxWeights_tendsto γ (fun a => (hγ a).le) hγsum
  have hτpos j a : 0 < τ j a := fieldApproxWeights_pos a0 γ j a
  have hτsum j : ∑ a, τ j a=1 := fieldApproxWeights_sum a0 γ j
  let R := finiteR ρ lam hρ hsum
  let F := (finiteMagneticFunctional R γ b).toReal
  let Fq := fun j => (finiteMagneticFunctional R (τ j) b).toReal
  have hF : Tendsto Fq atTop (𝓝 F) := finiteMagneticFunctional_tendsto_populations
    ρ lam hρ hsum τ γ b hτpos hτsum hγ hγsum hτ
  have hErr : Tendsto (fun j => 2*D*(∑ a, |γ a-τ j a|)) atTop (𝓝 0) := by
    have hh := (tendsto_finsetSum Finset.univ (fun a _ =>
      ((tendsto_const_nhds (x := γ a)).sub ((tendsto_pi_nhds.mp hτ) a)).abs)).const_mul (2*D)
    simpa only [sub_self,abs_zero,Finset.sum_const_zero,mul_zero] using hh
  intro ε hε
  obtain ⟨j,hjErr,hjF⟩ := ((hErr.eventually (Iio_mem_nhds (show 0<ε/4 by positivity))).and
    (Metric.tendsto_nhds.mp hF (ε/4) (by positivity))).exists
  let w := fun a => positiveApproxCount (γ a) j
  have hd : 0 < ∑ a, w a := fieldApproxDenominator_pos a0 γ j
  have hw a : (w a : ℝ)=(∑ a, w a : ℕ)*τ j a := by
    dsimp only [τ,fieldApproxWeights,w,fieldApproxDenominator]
    exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd.ne')).symm
  let cg := canonicalFieldLabel a0 w
  have hc : Tendsto (fun M a => (spinGroupSize (cg M) a : ℝ)/M) atTop (𝓝 (τ j)) :=
    canonicalFieldLabel_population a0 w hd
  have hlo := finite_count_template_pressure_lower hhaar hgauss hpub hm hn
    ρ lam hρ hsum hK hlam amax hmax μ spec hsp hspec hρspec e he w hd
    (τ j) (fun a => (hτpos j a).le) (hτsum j) hw cg b hc hD hb (ε/4) (by positivity)
  have hcomp := physical_mean_field_population_comparison (fun k => k+1) (fun _ => by omega)
    (fun k => μ (k+1)) (fun k i => lam (e (k+1) i)) (fun k => g (k+1))
    (fun k => cg (k+1)) γ (τ j) b (hg.comp (tendsto_add_atTop_nat 1))
    (hc.comp (tendsto_add_atTop_nat 1)) hD hb (ε/4) (by positivity)
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  have hev : ∀ᶠ k in atTop, F-ε≤P (k+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hlo,hcomp] with k hk hck
    have hh := (abs_le.mp hck).1
    rw [Real.dist_eq] at hjF
    have hFq := (abs_lt.mp hjF).1
    change Fq j-ε/4≤_ at hk
    change -_ ≤ P (k+1)-_ at hh
    linarith
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hev
  apply eventually_atTop.mpr
  refine ⟨J+1,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+1 := ⟨M-1,(Nat.sub_add_cancel (by omega)).symm⟩
  exact hJ k (by omega)

end InvariantIsing

end

end OAI
