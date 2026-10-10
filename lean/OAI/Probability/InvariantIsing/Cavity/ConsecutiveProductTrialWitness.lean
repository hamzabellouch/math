import OAI.Probability.InvariantIsing.Cavity.ConsecutiveProductWeakConsistency
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFixedMinimumLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGroupPartition
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPhysicalTrialLower

namespace OAI

/-! A single physical subsequence supplies both block self-consistency and the constrained pressure trial. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators
namespace InvariantIsing

theorem consecutive_product_minimum_trial_witness (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n : ℕ}
    (K : ℕ → ℕ) (hK : ∀ j, 2 ≤ K j)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < K j*n) (hNlim : Tendsto (fun j => K j*n) atTop atTop)
    (hN3 : ∀ j, 3≤K j*n)
    (g : (j : ℕ) → Fin (K j*n+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (K j*n+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (K j*n))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ K j*n+n)
    (μ : (j : ℕ) → Measure (Orthogonal (K j*n+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (K j*n)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (θ : ℕ → Measure (LabeledTree 0)) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a∈Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (K j*n) → ℝ) (hu : ∀ j i, u j i∈Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (K j) Cset)
          (consecutiveBlockConstraint_nonempty Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) (u j) (v j) ≤
      priorPerturbationObjective (cavityOrientedBaseLaw (hN j) (ν j))
        (restrictedZeroTreePrior (consecutiveBlockConstraint n (K j) Cset)
          (consecutiveBlockConstraint_nonempty Cset hCset))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 (fun _ => 0) u' v')
    (good : (j : ℕ) → Set (SpecialOrthogonal (K j*n+n)))
    (hgood : ∀ j, MeasurableSet (good j))
    (hp : Tendsto (fun j => ((μ j).map (cavityOrientationLift
      (Nat.add_pos_left (hN j) n))).real (good j)) atTop (𝓝 1))
    {L : ℝ} (hL : 0 < L)
    (hbound : ∀ j U, U ∈ good j → ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g j) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L)
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((K j*n : ℕ) : ℝ))
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/((K j*n : ℕ) : ℝ)) atTop (𝓝 ρ))
    (A_ : CavityFactorBlocks d n)
    (hA : A_ = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A_}) atTop (𝓝 0))
    (amax : Fin m) (hmax : ∀ a, lam a≤lam amax)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) :
    let Δ := fun j =>
      (∫ z, restrictedRotationLogMean
        (cavityProductSlice (consecutiveBlockConstraint n (K j) Cset) Cset)
        (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty Cset hCset) Cset hCset) z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
        (cavitySpectralGroup (g j)) (cavityBaseAmplitude (u j)) z.1 ∂(μ j).prod (θ j)) -
      ∫ z, restrictedRotationLogMean (consecutiveBlockConstraint n (K j) Cset)
        (consecutiveBlockConstraint_nonempty Cset hCset) z.2
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
  let I := fun j => cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
  let eig := fun j i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1
  let S := fun j => consecutiveBlockConstraint n (K j) Cset
  have hS j : (S j).Nonempty := consecutiveBlockConstraint_nonempty Cset hCset
  let M := 1+∑ a, |lam a|
  have hM : 0<M := by
    have hh : 0≤∑ a, |lam a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [M]
    linarith
  have heig j i : |eig j i|≤M := by
    have hh := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
    dsimp only [eig,M]
    linarith
  have hlam j a i (hi : i∈I j a) : eig j i=lam a := by
    have hi' : ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1=a := (Finset.mem_filter.mp hi).2
    change lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1=lam a
    rw [hi']
  have hmass : Tendsto (fun j a => ((I j a).card : ℝ)/((K j*n : ℕ) : ℝ)) atTop (𝓝 ρ) := by
    apply hρlim.congr
    intro j
    funext a
    rw [cavity_group_dimension_card]
  obtain ⟨Q,q,φ,hφ,hlim,hgg,hδ,hG,hE,hP,hnonneg,hoff,hdiag⟩ :=
    restricted_fixed_minimum_geometric_limit hhaar hgauss (fun j => K j*n) hN3 hNlim m
      S hS ν θ eig M hM heig I (fun _ => cavitySpectralGroup_pairwiseDisjoint _)
      (fun _ => cavitySpectralGroup_cover _) lam hlam ρ hmass u hu v hv hmin
  let p := spectralSpinQuantilePath Q hP hnonneg
  have hua j i : |cavityBaseAmplitude (u j) i|≤2 := cavityBaseAmplitude_bound (u j) (hu j) i
  have hva j a : |v j a|≤2 := abs_le.mpr ⟨by linarith [(hv j a).1],(hv j a).2⟩
  refine ⟨p,φ,hφ,?_,?_⟩
  · intro Φ
    exact consecutive_product_weak_self_consistency hpub (fun j => K (φ j)) (fun _ => 0)
      (fun j => hK (φ j)) Cset hCset (fun j => hN (φ j)) (hNlim.comp hφ.tendsto_atTop)
      (fun j => g (φ j)) (fun j => k (φ j)) (fun j => ek (φ j)) (fun j => e (φ j)) es B₀ a₀
      (fun j => hk (φ j)) (fun j => μG (φ j)) (fun j => l (φ j)) (fun j => w (φ j))
      (fun j => hg (φ j)) (fun j => hln (φ j)) (fun j => hw (φ j))
      (fun j => μ (φ j)) (fun j => ν (φ j)) (fun j => θ (φ j)) lam
      (fun j => v (φ j)) (fun j => hva (φ j)) (fun j => cavityBaseAmplitude (u (φ j)))
      (fun j => hua (φ j)) (fun j => good (φ j)) (fun j => hgood (φ j))
      (hp.comp hφ.tendsto_atTop) hL (fun j => hbound (φ j)) hd hn hB₀ ρ hρ hρsum hperp
      (fun j => hgroups (φ j)) (fun a => (hdims a).comp hφ.tendsto_atTop) hc
      (fun j => hcG (φ j)) (hρlim.comp hφ.tendsto_atTop) A_ hA
      (fun δ hδ => (hprob δ hδ).comp hφ.tendsto_atTop)
      Q hlim hgg hG (fun a => (q a : ℝ)) (fun a => (q a).property.1) hδ hE hP hnonneg hoff hdiag
      amax hmax Φ
  · have hh := restricted_physical_trial_lower hn (fun j => K (φ j)*n) (fun _ => 0)
      (fun j => S (φ j)) (fun j => hS (φ j)) Cset hCset
      (fun j => hN (φ j)) (hNlim.comp hφ.tendsto_atTop)
      (fun j => g (φ j)) (fun j => k (φ j)) (fun j => e (φ j)) (fun j => ek (φ j)) es B₀
      (fun a j => l (φ j) a) (fun a j => w (φ j) a)
      (fun j => hg (φ j)) (fun j => hln (φ j)) (fun j => hw (φ j)) a₀ (fun j => hk (φ j))
      (fun j => hgroups (φ j)) (fun a => (hdims a).comp hφ.tendsto_atTop)
      (fun j => μ (φ j)) (fun j => ν (φ j)) (fun j => θ (φ j)) (fun j => μG (φ j))
      lam (fun j => v (φ j)) (fun j => cavityBaseAmplitude (u (φ j)))
      (fun j => hva (φ j)) (fun j => hua (φ j)) hc (fun j => hcG (φ j)) ρ hρ hρsum
      (hρlim.comp hφ.tendsto_atTop) Q hlim hgg hG (fun a => (q a : ℝ))
      (fun a => (q a).property.1) hδ hE hP hnonneg hoff hdiag
      (cavityCompressionLimitFrame es B₀) (cavityCompressionLimitFrame_gram es B₀ hB₀)
      (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
      (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
      amax hmax counts hcounts_le hcounts hcounts_rho
      (fun ε hε => by simpa only [hA, Function.comp_def] using (hprob ε hε).comp hφ.tendsto_atTop)
    exact hh

end InvariantIsing

end

end OAI
