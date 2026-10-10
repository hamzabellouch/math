import OAI.Probability.InvariantIsing.Cavity.CavityRationalAllSizes
import OAI.Probability.InvariantIsing.Cavity.CavityMultiplicityTransport
import OAI.Probability.InvariantIsing.Core.PositiveRationalApproximation
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralContinuity

namespace OAI

/-! The finite-alphabet mean limit along arbitrary diverging dimensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_selected_dimensions_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun k a => ((cavitySpectralGroup (g k) a).card : ℝ)/D k) atTop (𝓝 ρ)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal) := by
  have hm0 : 0 < m := by omega
  let τ := positiveApproxWeights ρ
  have hτpos j a : 0 < τ j a := positiveApproxWeights_pos hm0 ρ j a
  have hτsum j : ∑ a, τ j a=1 := positiveApproxWeights_sum hm0 ρ j
  have hτ : Tendsto τ atTop (𝓝 ρ) := positiveApproxWeights_tendsto ρ (fun a => (hρ a).le) hρsum
  let F := fun j => (variationalFunctional (finiteR (τ j) lam (hτpos j) (hτsum j))).toReal
  let L := (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal
  have hF : Tendsto F atTop (𝓝 L) :=
    finiteVariational_tendsto_weights τ ρ lam hτpos hτsum hρ hρsum hτ
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound a : |lam a| ≤ K :=
    Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hdiam a b : |lam a-lam b| ≤ 2*K :=
    (abs_sub _ _).trans (by linarith [hbound a,hbound b])
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := ε/(3*(2*K+1))
  have hR : 0 < R := by dsimp only [R]; positivity
  have hrel : ∀ᶠ j in atTop, ∀ a, |ρ a-τ j a|/min (ρ a) (τ j a) < R := by
    apply Filter.eventually_all.mpr
    intro a
    have ht := (tendsto_pi_nhds.mp hτ) a
    have hconst : Tendsto (fun _ : ℕ => ρ a) atTop (𝓝 (ρ a)) := tendsto_const_nhds
    have hh := ((hconst.sub ht).abs).div
      (hconst.min ht) (by simpa only [min_self] using (hρ a).ne')
    change Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop
      (𝓝 (|ρ a-ρ a|/min (ρ a) (ρ a))) at hh
    have hz : Tendsto (fun j => |ρ a-τ j a|/min (ρ a) (τ j a)) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero, zero_div] using hh
    exact hz.eventually (Iio_mem_nhds hR)
  obtain ⟨j,hj,hFj⟩ := (hrel.and (Metric.tendsto_nhds.mp hF (ε/3) (by positivity))).exists
  let s := fun a => positiveApproxCount (ρ a) j
  let n := positiveApproxDenominator ρ j
  have hn : 0 < n := positiveApproxDenominator_pos hm0 ρ j
  have hs a : 0 < s a := positiveApproxCount_pos (ρ a) j
  have hsum : ∑ a, s a=n := rfl
  let A := fun N => cavityResidueLabel hm0 s hsum N
  have hAlim : Tendsto (fun k a => ((cavitySpectralGroup (A (D k)) a).card : ℝ)/(D k : ℝ))
      atTop (𝓝 (τ j)) :=
    (cavity_canonical_mass_tendsto hm0 hn s hsum).comp hDlim
  have hglim := hρlim
  have hcounts := eventually_relative_count_bound D hD
    (fun k a => (cavitySpectralGroup (g k) a).card)
    (fun k a => (cavitySpectralGroup (A (D k)) a).card) ρ (τ j) hρ (hτpos j) hglim hAlim R hj
  have hgSurj := eventually_surjective_label hD g ρ hρ hglim
  have hASurj := eventually_surjective_label hD (fun k => A (D k)) (τ j) (hτpos j) hAlim
  have hP := (cavity_rational_all_sizes_tendsto hhaar hgauss hpub hm hn s hs hsum μ lam).comp
    hDlim
  have hPsmall := Metric.tendsto_nhds.mp hP (ε/3) (by positivity)
  filter_upwards [hcounts,hgSurj,hASurj,hPsmall] with k hk hgk hAk hPk
  have hc := cavity_meanPressure_multiplicity_comparison (hD k) (μ (D k))
    (g k) (A (D k)) hgk hAk lam (fun _ => 0) K hbound (2*K) R (by positivity) hR.le hdiam hk
  let P := ∫ V, rotatedPressure (fun i => lam (g k i)) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)
  let Q := ∫ V, rotatedPressure (fun i => lam (A (D k) i)) (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)
  have hPQ : |P-Q| ≤ 2*K*R/2 := by simpa only [abs_sub_comm] using hc
  have hQL : |Q-F j| < ε/3 := by
    rw [Real.dist_eq] at hPk
    change |Q-F j| < ε/3 at hPk
    exact hPk
  have hFL : |F j-L| < ε/3 := by simpa only [Real.dist_eq] using hFj
  have hsmall : 2*K*R/2 < ε/3 := by
    have hmul : R*(3*(2*K+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  change dist P L < ε
  rw [Real.dist_eq]
  have ht := abs_sub_le P Q L
  have ht' := abs_sub_le Q (F j) L
  linarith

end InvariantIsing

end

end OAI
