import OAI.Probability.InvariantIsing.Cavity.CavityWindowVariationalLower
import OAI.Probability.InvariantIsing.Cavity.CavityFixedMinimumLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGroupPartition
import OAI.Probability.InvariantIsing.Cavity.CavitySubsequenceLower

namespace OAI

/-! The actual finite pressure minima imply the physical variational
increment lower bound. No Gibbs-array limit is assumed here. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_window_minimum_variational_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N : ℕ → ℕ) (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (hN : ∀ j, 3 ≤ N j) (hNlim : Tendsto N atTop atTop)
    (g : (j : ℕ) → Fin (N j+n) → Fin m) (k : ℕ → Fin m → ℕ)
    (ek : ∀ j a, {i : Fin (N j+n) // g j i = a} ≃ Fin (k j a+n))
    (e : (j : ℕ) → (((a : Fin m) × Fin (k j a)) ⊕ Fin d) ≃ Fin (N j))
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (hk : ∀ j a, d ≤ k j a)
    (μG : (j : ℕ) → (a : Fin m) → Measure (Orthogonal (cavityBaseGroupDimension (k j) a₀ a)))
    [∀ j a, IsProbabilityMeasure (μG j a)] [∀ j a, (μG j a).IsMulRightInvariant]
    (l w : ℕ → Fin m → ℕ)
    (hg : ∀ j a i, g j i=a ↔ l j a ≤ i.val ∧ i.val < w j a)
    (hln : ∀ j a, l j a+n ≤ w j a) (hw : ∀ j a, w j a ≤ N j+n)
    (μ : (j : ℕ) → Measure (Orthogonal (N j+n)))
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, (μ j).IsMulRightInvariant]
    (ν : (j : ℕ) → Measure (Orthogonal (N j)))
    [∀ j, IsProbabilityMeasure (ν j)] [∀ j, (ν j).IsMulRightInvariant]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, v j a ∈ Set.Icc (1 : ℝ) 2)
    (u : (j : ℕ) → Fin (N j) → ℝ) (hu : ∀ j i, u j i ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN j; omega) (ν j))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 depth b (fun _ => 0) (u j) (v j) ≤
      tensorPerturbationObjective (cavityOrientedBaseLaw (by have := hN j; omega) (ν j))
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1) (fun _ => 0)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1))
        1 depth b (fun _ => 0) u' v')
    (hd : 0 < d) (hn : 0 < n)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (ρl ρw : Fin m → ℝ) (hρdef : ρ=fun a => ρw a-ρl a)
    (hwlim : ∀ a, Tendsto (fun r => w r a) atTop atTop)
    (hllim : ∀ a, (∀ r, l r a=0) ∨ Tendsto (fun r => l r a) atTop atTop)
    (hρl : ∀ a, Tendsto (fun r => (l r a : ℝ)/(N r+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun r => (w r a : ℝ)/(N r+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => ρ a • 1)).transpose * B₀ = 0)
    (hgroups : ∀ j a, 0 < cavityBaseGroupDimension (k j) a₀ a)
    (hdims : ∀ a, Tendsto (fun j => cavityBaseGroupDimension (k j) a₀ a) atTop atTop)
    {c : ℝ} (hc : 0 < c)
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let θ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (cavityBaseAmplitude (u r)) z.1 ∂(μ r).prod θ) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (cavityBaseAmplitude (u r)) z.1 ∂(ν r).prod θ
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro θ Δ
  let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
  let I := fun r => cavitySpectralGroup (fun i => ((E r).symm i).1)
  let eig := fun r i => lam ((E r).symm i).1
  let K := 1+∑ a, |lam a|
  have hK : 0<K := by
    have hs : 0≤∑ a, |lam a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [K]
    linarith
  have hKeig r i : |eig r i|≤K := by
    have hs := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (((E r).symm i).1))
    dsimp only [eig, K]
    linarith
  have hlabel r a i (hi : i∈I r a) : eig r i=lam a := by
    have he : ((E r).symm i).1=a := (Finset.mem_filter.mp hi).2
    change lam ((E r).symm i).1=lam a
    rw [he]
  have hmass : Tendsto (fun r a => ((I r a).card : ℝ)/N r) atTop (𝓝 ρ) := by
    apply hρlim.congr
    intro r
    funext a
    rw [cavity_group_dimension_card]
  have hpos r : 0<N r := by have := hN r; omega
  have hua r j : |cavityBaseAmplitude (u r) j|≤2 := cavityBaseAmplitude_bound (u r) (hu r) j
  have hva r a : |v r a|≤2 := abs_le.mpr ⟨by linarith [(hv r a).1], (hv r a).2⟩
  have hlower := cavity_eventual_lower_of_subsequence (fun r => (n : ℝ)⁻¹*Δ r)
    (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal (by
      intro φ hφ
      obtain ⟨ψ,hψ,Q,q,hlim,hgg,hδ,hG,hE,hP,hnonneg,hoff,hdiag⟩ :=
        cavity_fixed_minimum_geometric_limit hhaar hgauss (fun r => N (φ r))
          (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop) m depth b hb
          (fun r => ν (φ r)) (fun r => eig (φ r)) K hK (fun r => hKeig (φ r))
          (fun r => I (φ r)) (fun r => cavitySpectralGroup_pairwiseDisjoint _)
          (fun r => cavitySpectralGroup_cover _) lam (fun r => hlabel (φ r))
          ρ (hmass.comp hφ.tendsto_atTop) (fun r => u (φ r)) (fun r => v (φ r))
          (fun r => hu (φ r)) (fun r => hv (φ r)) (fun r => hmin (φ r))
      let χ := φ ∘ ψ
      have hχ : StrictMono χ := hφ.comp hψ
      have hh := cavity_window_variational_lower hpub (fun r => N (χ r)) (fun _ => depth)
        (fun r => hpos (χ r)) (hNlim.comp hχ.tendsto_atTop)
        (fun r => g (χ r)) (fun r => k (χ r)) (fun r => ek (χ r)) (fun r => e (χ r))
        es B₀ a₀ (fun r => hk (χ r)) (fun r => μG (χ r))
        (fun r => l (χ r)) (fun r => w (χ r)) (fun r => hg (χ r))
        (fun r => hln (χ r)) (fun r => hw (χ r)) (fun r => μ (χ r)) (fun r => ν (χ r))
        (fun _ => θ) lam (fun r => v (χ r)) (fun r => hva (χ r))
        (fun r => cavityBaseAmplitude (u (χ r))) (fun r => hua (χ r)) hd hn hB₀
        ρ hρ hρsum ρl ρw hρdef (fun a => (hwlim a).comp hχ.tendsto_atTop)
        (fun a => (hllim a).elim (fun h => Or.inl (fun r => h (χ r)))
          (fun h => Or.inr (h.comp hχ.tendsto_atTop)))
        (fun a => (hρl a).comp hχ.tendsto_atTop) (fun a => (hρw a).comp hχ.tendsto_atTop)
        hperp (fun r => hgroups (χ r)) (fun a => (hdims a).comp hχ.tendsto_atTop)
        hc (fun r => hcG (χ r)) (hρlim.comp hχ.tendsto_atTop)
        Q hlim hgg hG (fun a => (q a : ℝ)) (fun a => (q a).property.1) hδ
        hE hP hnonneg hoff hdiag a ha counts hcounts_le hcounts hcounts_rho R
      refine ⟨ψ,hψ,?_⟩
      intro ε hε
      filter_upwards [hh ε hε] with r hr
      change (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-
        (n : ℝ)⁻¹*Δ (φ (ψ r))<ε at hr
      linarith)
  intro ε hε
  filter_upwards [hlower ε hε] with r hr
  linarith

end InvariantIsing

end

end OAI
