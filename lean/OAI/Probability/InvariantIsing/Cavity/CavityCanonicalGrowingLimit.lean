import OAI.Probability.InvariantIsing.Cavity.CavityGrowingGeometricLimit
import OAI.Probability.InvariantIsing.Cavity.CavityGroupPartition

namespace OAI

/-! The growing-depth physical minimizing sequence has every geometric
and Ward property required by the cavity lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_canonical_growing_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3≤N k) (hNlim : Tendsto N atTop atTop)
    (m d : ℕ) (depth : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ r, CascadeExponents (depth r) (b r))
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (k : ℕ → Fin m → ℕ)
    (e : (r : ℕ) → (((a : Fin m) × Fin (k r a)) ⊕ Fin d) ≃ Fin (N r))
    (a₀ : Fin d → Fin m) (lam ρ : Fin m → ℝ)
    (hρ : Tendsto (fun r a => (cavityBaseGroupDimension (k r) a₀ a : ℝ)/N r) atTop (𝓝 ρ)) :
    let E := fun r => cavityBaseGroupEquiv (k r) (e r) a₀
    let I := fun r => cavitySpectralGroup (fun i => ((E r).symm i).1)
    let eig := fun r i => lam ((E r).symm i).1
    ∃ φ ψ : ℕ → ℕ, StrictMono φ ∧ StrictMono ψ ∧
    ∃ u : (r : ℕ) → Fin (N (φ r)) → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ r j, u r j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ r a, v r a ∈ Set.Icc (1 : ℝ) 2) ∧
    ∃ Q : ProbabilityMeasure (SpectralArray (m+1)), ∃ q : Fin (m+1) → Set.Icc (0 : ℝ) 1,
      Tendsto (fun r => cavityRotationArrayLaw (μ (φ r))
        (labeledCascadeLaw (depth (ψ r)) (b (ψ r)) : Measure (LabeledTree (depth (ψ r))))
        (diagonalPerturbedEigenvalues (eig (φ r)) (I (φ r)) (v r) 1)
        (I (φ r)) (cavityBaseAmplitude (u r))) atTop (𝓝 Q) ∧
      HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m+1))) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ i a, (x (i,i) a : ℝ)=q a) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralGram x) ∧
      (∀ e : ℕ → ℕ, Function.Injective e →
        (Q : Measure (SpectralArray (m+1))).map (permuteSpectralArray e)=Q) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), SpectralPartitionGeometry m x) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m+1))), ∀ a, 0≤(x (0,1) a : ℝ)) ∧
      (∀ a b₀, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ B : ℝ, 0≤B → (∀ r, |Φ r|≤B) →
        spectralOffWardResidual Q ρ lam a b₀ Φ=0) ∧
      (∀ a b₀, spectralDiagonalWardResidual Q ρ lam a b₀=0) := by
  intro E I eig
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
    apply hρ.congr
    intro r
    funext a
    rw [cavity_group_dimension_card]
  exact cavity_growing_depth_geometric_limit hhaar hgauss N hN hNlim m depth b hb μ
    eig K hK hKeig I (fun r => cavitySpectralGroup_pairwiseDisjoint _)
    (fun r => cavitySpectralGroup_cover _) lam hlabel ρ hmass

end InvariantIsing

end

end OAI
