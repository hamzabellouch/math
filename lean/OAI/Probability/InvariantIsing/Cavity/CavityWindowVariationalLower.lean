import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalVariationalLower
import OAI.Probability.InvariantIsing.Cavity.CavityWindowInputs

namespace OAI

/-! The variational lower bound with compression convergence and its
good event discharged by the actual contiguous-window laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_window_variational_lower (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
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
    (θ : (j : ℕ) → Measure (LabeledTree (depth j))) [∀ j, IsProbabilityMeasure (θ j)]
    (lam : Fin m → ℝ) (v : ℕ → Fin m → ℝ)
    (hv : ∀ j a, |v j a| ≤ 2) (u : ℕ → ℕ → ℝ) (hu : ∀ j i, |u j i| ≤ 2)
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
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => cavityRotationArrayLaw (ν j) (θ j)
      (diagonalPerturbedEigenvalues
        (fun i => lam ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)
        (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (v j) 1)
      (cavitySpectralGroup (fun i => ((cavityBaseGroupEquiv (k j) (e j) a₀).symm i).1)) (u j))
      atTop (𝓝 Q₀))
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q₀ : Measure (SpectralArray (m+1))))
    (hG : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralGram x)
    (δ : Fin (m+1) → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ i j, (x (i,i) j : ℝ) = δ j)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q₀ : Measure (SpectralArray (m+1))).map (permuteSpectralArray e) = Q₀)
    (hP : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x)
    (hnonneg : ∀ᵐ x ∂(Q₀ : Measure (SpectralArray (m+1))), ∀ j, 0 ≤ (x (0,1) j : ℝ))
    (hoff : ∀ j l, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0 ≤ B → (∀ t, |Φ t| ≤ B) →
      spectralOffWardResidual Q₀ ρ lam j l Φ = 0)
    (hdiag : ∀ j l, spectralDiagonalWardResidual Q₀ ρ lam j l = 0)
    (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a≤n)
    (hcounts : ∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ)=(n : ℝ)*ρ a) (R : Rotation n) :
    let Δ := fun r =>
      (∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) z.1 ∂(μ r).prod (θ r)) -
      ∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ ((e r).symm i)))
          (cavityBaseGroup (k r) (e r) a₀) (v r) 1)
        (cavityBaseGroup (k r) (e r) a₀) (u r) z.1 ∂(ν r).prod (θ r)
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal-(n : ℝ)⁻¹*Δ r<ε := by
  intro Δ
  subst ρ
  have hsumlim : Tendsto (fun r => N r+n) atTop atTop :=
    (tendsto_add_atTop_nat n).comp hNlim
  obtain ⟨⟨L,hL,hgood⟩,hprob⟩ := cavity_window_inputs es lam a₀ B₀ hB₀ N
    (fun r => Nat.add_pos_left (hN r) n) (fun a r => l r a) (fun a r => w r a) g
    (fun a r => hg r a) hsumlim hwlim hllim
    (fun a r => by have := hln r a; omega)
    (fun a r => by have := hln r a; have := hw r a; omega)
    (fun a r => hw r a) ρl ρw hρ hρsum hρl hρw hperp μ
  let A : CavityFactorBlocks d n :=
    ((cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityCompressionLimitFrame es B₀-Matrix.diagonal (fun j => lam (a₀ j)),
     (cavityCompressionLimitFrame es B₀).transpose*cavityRepeatedSpectrum (n := n) lam*
        cavityLimitingStack (n := n) (fun a => ρw a-ρl a),
     (finiteR (fun a => ρw a-ρl a) lam hρ hρsum 0) • 1)
  exact cavity_physical_variational_lower hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu (fun r => cavityCompressionGoodEvent (g r) L)
    (fun r => measurableSet_cavityCompressionGoodEvent (g r) L) hgood hL
    (fun _ _ hU => hU) hd hn hB₀ (fun a => ρw a-ρl a) hρ hρsum hperp
    hgroups hdims hc hcG hρlim A rfl hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg
    hoff hdiag a ha counts hcounts_le hcounts hcounts_rho R

end InvariantIsing

end

end OAI
