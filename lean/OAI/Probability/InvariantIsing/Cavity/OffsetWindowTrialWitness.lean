import OAI.Probability.InvariantIsing.Cavity.OffsetProductTrialWitness
import OAI.Probability.InvariantIsing.Cavity.CavityWindowInputs

namespace OAI

/-! Haar window theorems supply the physical compression hypotheses of block consistency. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators
namespace InvariantIsing

theorem offset_window_minimum_trial_witness (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n r₀ : ℕ}
    (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j) (hKlim : Tendsto K atTop atTop)
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < r₀+K j*n) (hNlim : Tendsto (fun j => r₀+K j*n) atTop atTop)
    (hN3 : ∀ j, 3≤r₀+K j*n)
    (g : (j : ℕ) → Fin (r₀+K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (r₀+K j*n+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (r₀+K j*n))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ r₀+K j*n+n)
    (μ : (j : ℕ) → Measure (Orthogonal (r₀+K j*n+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (r₀+K j*n)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (r₀+K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) (u j) (v j) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (offsetBlockConstraint (K j) R Cset)
          (offsetBlockConstraint_nonempty R hR Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) u' v')
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun j => w j a) atTop atTop)
    (hllim : ∀ a, (∀ j, l j a=0) ∨ Tendsto (fun j => l j a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun j => (l j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun j => (w j a : ℝ)/(r₀+K j*n+n : ℕ)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ))
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((r₀+K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
    let Δ := fun j =>
      (∫ z, restrictedRotationLogMean
        (cavityProductSlice (offsetBlockConstraint (K j) R Cset) Cset)
        (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR Cset hCset) Cset hCset) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
        (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
      ∫ z, restrictedRotationLogMean (offsetBlockConstraint (K j) R Cset)
        (offsetBlockConstraint_nonempty R hR Cset hCset) z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e j).symm i)))
          (cavityBaseGroup (k j) (e j) a₀) (v j) 1)
        (cavityBaseGroup (k j) (e j) a₀) (cavityBaseAmplitude (u j)) z.1 ∂(ν j).prod (θ j)

    ∃ (p : OverlapPath) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ Φ : ℝ →ᵇ ℝ,
        Tendsto (fun r => ∫ t, Φ (cavityStrictUniformPath p r t) *
          (restrictedBlockOverlapPath hn Cset hCset (cavityStrictUniformField ρ lam hρ hρsum p r) t -
            cavityStrictUniformPath p r t) ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        constrainedBlockValue Cset (cavityStrictUniformField ρ lam hρ hρsum p r)+
          fieldPairing (cavityStrictUniformPath p r) (cavityStrictUniformField ρ lam hρ hρsum p r)/2+
          spectralFunctional (finiteR ρ lam hρ hρsum) (cavityStrictUniformPath p r)-
          (n : ℝ)⁻¹*(Δ (φ r)+(Real.log Cset.card-n*Real.log 2)) < ε := by
  intro Δ
  subst ρ
  have hsumlim : Tendsto (fun j => r₀+K j*n+n) atTop atTop :=
    (tendsto_add_atTop_nat n).comp hNlim
  obtain ⟨⟨L,hL,hgood⟩,hprob⟩ := cavity_window_inputs es lam a₀ B₀ hB₀ (fun j => r₀+K j*n)
    (fun j => Nat.add_pos_left (hN j) n) (fun a j => l j a) (fun a j => w j a) g
    (fun a j => hg j a) hsumlim hwlim hllim
    (fun a j => by have := hln j a; omega)
    (fun a j => by have := hln j a; have := hw j a; omega)
    (fun a j => hw j a) ρl ρw hρ hρsum (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρw a) hperp μ
  let A : CavityFactorBlocks d n :=
    ((cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityCompressionLimitFrame es B₀-Matrix.diagonal (fun j => lam (a₀ j)),
     (cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) (fun a => ρw a-ρl a),
     (finiteR (fun a => ρw a-ρl a) lam hρ hρsum 0) • 1)
  exact offset_product_minimum_trial_witness hhaar hgauss hpub K hK hKlim R hR Cset hCset hN hNlim hN3
    g k ek e es B₀ a₀ hk μG l w hg hln hw μ ν θ lam v hv u hu hmin
    (fun j => cavityCompressionGoodEvent (g j) L)
    (fun j => measurableSet_cavityCompressionGoodEvent (g j) L) hgood hL
    (fun _ _ hU => hU) hd hn hB₀ (fun a => ρw a-ρl a) hρ hρsum hperp
    hgroups hdims hc hcG hρlim A rfl hprob amax hmax counts hcounts_le hcounts hcounts_rho

end InvariantIsing

end

end OAI
