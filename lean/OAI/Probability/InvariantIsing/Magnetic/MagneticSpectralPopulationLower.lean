import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldPopulationLower
import OAI.Probability.InvariantIsing.Magnetic.MagneticSpectralContinuity

namespace OAI

/-! Rational approximation of the spectral populations gives the physical
finite-field lower bound for arbitrary positive real populations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_physical_field_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m)
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
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
  have hm0 : 0 < m := by omega
  let τ := positiveApproxWeights ρ
  have hτpos j a : 0 < τ j a := positiveApproxWeights_pos hm0 ρ j a
  have hτsum j : ∑ a, τ j a=1 := positiveApproxWeights_sum hm0 ρ j
  have hτ : Tendsto τ atTop (𝓝 ρ) := positiveApproxWeights_tendsto ρ (fun a => (hρ a).le) hsum
  let F := (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal
  let Fq := fun j => (finiteMagneticFunctional (finiteR (τ j) lam (hτpos j) (hτsum j)) γ b).toReal
  have hF : Tendsto Fq atTop (𝓝 F) := finiteMagneticFunctional_tendsto_weights
    τ ρ lam hτpos hτsum hρ hsum hτ γ b (fun a => (hγ a).le) hγsum
  intro ε hε
  let r := ε/(4*(2*K+1))
  have hr : 0 < r := div_pos hε (by positivity)
  have hrel : ∀ᶠ j in atTop, ∀ a, |ρ a-τ j a|/min (ρ a) (τ j a)<r := by
    apply Filter.eventually_all.mpr
    intro a
    have ht := (tendsto_pi_nhds.mp hτ) a
    have hc : Tendsto (fun _ : ℕ => ρ a) atTop (𝓝 (ρ a)) := tendsto_const_nhds
    have hh := ((hc.sub ht).abs).div (hc.min ht) (by simpa only [min_self] using (hρ a).ne')
    change Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop
      (𝓝 (|ρ a-ρ a|/min (ρ a) (ρ a))) at hh
    have hz : Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop (𝓝 0) := by
      simpa only [sub_self,abs_zero,zero_div] using hh
    exact hz.eventually (Iio_mem_nhds hr)
  obtain ⟨j,hj,hjF⟩ := (hrel.and (Metric.tendsto_nhds.mp hF (ε/4) (by positivity))).exists
  let s := fun a => positiveApproxCount (ρ a) j
  let n := positiveApproxDenominator ρ j
  have hn : 0 < n := positiveApproxDenominator_pos hm0 ρ j
  have hs a : 0 < s a := positiveApproxCount_pos (ρ a) j
  have hsn : ∑ a, s a=n := rfl
  have hcount a : (s a : ℝ)=(n : ℝ)*τ j a := by
    exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')).symm
  let A := fun M => cavityResidueLabel hm0 s hsn M
  have hA : Tendsto (fun M a => (spinGroupSize (A M) a : ℝ)/M) atTop (𝓝 (τ j)) :=
    cavity_canonical_mass_tendsto hm0 hn s hsn
  have hlo := finite_rational_spectrum_field_pressure_lower hhaar hgauss hpub hm hn
    (τ j) lam (hτpos j) (hτsum j) hK hlam amax hmax μ s hs hsn hcount A hA γ hγ hγsum
    g b hg hD hb (ε/4) (by positivity)
  have he' := he.comp (tendsto_add_atTop_nat 1)
  have hA' := hA.comp (tendsto_add_atTop_nat 1)
  have hcounts := eventually_relative_count_bound (fun k => k+1) (fun _ => by omega)
    (fun k a => spinGroupSize (e (k+1)) a) (fun k a => spinGroupSize (A (k+1)) a)
    ρ (τ j) hρ (hτpos j) he' hA' r hj
  have hesurj := eventually_surjective_label (fun _ => by omega) (fun k => e (k+1)) ρ hρ he'
  have hAsurj := eventually_surjective_label (fun _ => by omega) (fun k => A (k+1)) (τ j) (hτpos j) hA'
  let P := fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
    (fun i => b (g M i)) ∂μ M
  have hsmall : 2*K*r/2<ε/4 := by
    have hh : r*(4*(2*K+1))=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hev : ∀ᶠ k in atTop, F-ε≤P (k+1) := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hlo,hcounts,hesurj,hAsurj] with k hl hk hes hAs
    have hcomp := cavity_meanPressure_multiplicity_comparison (by omega : 0 < k+1) (μ (k+1))
      (e (k+1)) (A (k+1)) hes hAs lam (fun i => b (g (k+1) i)) K hlam
      (2*K) r (by positivity) hr.le
      (fun a b => (abs_sub _ _).trans (by linarith [hlam a,hlam b])) hk
    have hh := (abs_le.mp hcomp).2
    rw [Real.dist_eq] at hjF
    have hFq := (abs_lt.mp hjF).1
    change Fq j-ε/4≤_ at hl
    change _-P (k+1)≤_ at hh
    linarith
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hev
  apply eventually_atTop.mpr
  refine ⟨J+1,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+1 := ⟨M-1,(Nat.sub_add_cancel (by omega)).symm⟩
  exact hJ k (by omega)

end InvariantIsing

end

end OAI
