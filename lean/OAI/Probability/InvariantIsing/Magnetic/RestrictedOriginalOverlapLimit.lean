import OAI.Probability.InvariantIsing.Magnetic.RestrictedOriginalFullComparison
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPhysicalOverlapCutoff
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralCutoffRadii
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionLimitGeometry
import OAI.Probability.InvariantIsing.Cavity.CavitySplitOverlapTest

namespace OAI

/-! The actual full model, including the original random tree and both
perturbations, has the scalar-field two-spin limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem restricted_original_split_overlap_limit (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {m d n : ℕ}
    (N depth : ℕ → ℕ)
    (S : (j : ℕ) → Finset (Spin (N j))) (hS : ∀ j, (S j).Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty) (hN : ∀ j, 0 < N j) (hNlim : Tendsto N atTop atTop)
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
    {M₀ : ℝ} (hmean : ∀ j (T : LabeledTree (depth j)), restrictedCavityFullDisorderTest
      (cavityProductSlice (S j) Cset) (cavityProductSlice_nonempty (S j) (hS j) Cset hCset)
      ((μ j).map (cavityOrientationLift (Nat.add_pos_left (hN j) n))) T
      (diagonalPerturbedEigenvalues (fun i => lam (g j i)) (cavitySpectralGroup (g j)) (v j) 1)
      (cavitySpectralGroup (g j)) (u j)
      (cavityProjectionAxesTest (cavitySpectralGroup (g j)) (Fin.natAdd (N j))) ≤ M₀)
    (good : (j : ℕ) → Set (SpecialOrthogonal (N j+n)))
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
    (hcG : ∀ j a, c ≤ (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j)
    (hρlim : Tendsto (fun j a => (cavityBaseGroupDimension (k j) a₀ a : ℝ)/N j) atTop (𝓝 ρ))
    (A : CavityFactorBlocks d n)
    (hA : A = ((cavityCompressionLimitFrame es B₀).transpose *
      cavityRepeatedSpectrum (n := n) lam * cavityCompressionLimitFrame es B₀ -
      Matrix.diagonal (fun i => lam (a₀ i)),
      (cavityCompressionLimitFrame es B₀).transpose * cavityRepeatedSpectrum (n := n) lam *
        cavityLimitingStack (n := n) ρ,
      (finiteR ρ lam hρ hρsum 0) • (1 : Matrix (Fin n) (Fin n) ℝ)))
    (hprob : ∀ δ > 0, Tendsto (fun j => (μ j).real
      {U | δ < cavityFactorDeviation
        (cavityCompressionFactorBlocks es lam (fun i => lam (a₀ i)) B₀
          (cavityCompressionGrams (g j) U)) A}) atTop (𝓝 0))
    (Q₀ : ProbabilityMeasure (SpectralArray (m+1)))
    (hlim : Tendsto (fun j => restrictedRotationArrayLaw (S j) (hS j) (ν j) (θ j)
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
    (Φ : ℝ →ᵇ ℝ) :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r =>
      (∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset) ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
        (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
        (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r) -
      ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  let E := fun j => cavityBaseGroupEquiv (k j) (e j) a₀
  let eig := fun j => diagonalPerturbedEigenvalues (fun i => lam ((E j).symm i).1)
    (cavitySpectralGroup (fun i => ((E j).symm i).1)) (v j) 1
  let B := cavityCompressionLimitFrame es B₀
  let F := fun j (σ : Fin 2 → (Spin (N j) × LabeledLeaf (depth j)) × Spin n) =>
    Φ (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  have hF j σ : |F j σ| ≤ ‖Φ‖ := by
    simpa only [F,abs_mul,abs_spinValue,mul_one,one_mul,Real.norm_eq_abs] using
      Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((σ 0).1.1,(σ 1).1.1))
  obtain ⟨b,hblim,hb⟩ := cavity_spectral_common_cutoff_radii Q₀ ρ (fun i : Fin d => (a₀ i,i))
  have hbpos j := (hb j).1
  have hnull j r := (hb j).2 r
  have hfinite := restricted_physical_overlap_cutoff hpub N depth hN S hS
    (fun j => cavityBaseGroupDimension (k j) a₀) hgroups hdims E ν θ μG
    (fun j => cavityCanonicalGroupFrame (k j) (e j) a₀ (hk j))
    (fun j a => cavityCanonicalGroupFrame_gram (k j) (e j) a₀ (hk j) a)
    eig u hc hcG ρ lam hρ hρsum hρlim Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a₀ (fun i => (a₀ i,i)) (fun i j hij => congrArg Prod.snd hij) (fun _ => rfl)
    hd hn Cset hCset B (cavityCompressionLimitFrame_gram es B₀ hB₀)
    (cavityCompressionLimitFrame_perp es B₀ ρ (fun a => (hρ a).le) hperp)
    (cavityCompressionLimitFrame_complete es B₀ hB₀ ρ (fun a => (hρ a).le) hρsum hperp)
    a ha Φ Φ.continuous (fun x => by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm x)
    b hbpos hblim hnull
  have horig := restricted_original_full_haar_comparison N depth S hS Cset hCset hN hNlim g k ek e es B₀ a₀ hk
    (fun j => Measure.pi (μG j)) l w hg hln hw μ ν θ lam v hv u hu 1 hmean good hgood hp hL hbound
    (norm_nonneg Φ) F hF A hprob b hbpos hblim
  dsimp only at hfinite horig
  rw [hA] at horig
  simp only [one_smul] at horig
  let cut := fun j r => ∫ ω, cavityWeightedReplicaMean
    ((restrictedRotationProbability (S r) (hS r) (eig r) (cavitySpectralGroup (fun i => ((E r).symm i).1))
      (u r) ω.1).prod (restrictedSpinPrior Cset hCset))
    (fun x => cavityHaarRestrictedWeight (fun i => (a₀ i,i))
      (cavityRotationVectors (cavityBaseGroupDimension (k r) a₀) (E r))
      (cavityCanonicalGroupFrame (k r) (e r) a₀ (hk r))
      A.1 A.2.1 A.2.2 (cavityFactorSize A.1 A.2.1 A.2.2*(1+(b j)^2)) (b j) (ω,x)) (F r)
    ∂(((ν r).prod (θ r)).prod gaussianCoordinates).prod (Measure.pi (μG r))
  let full := fun r => ∫ T, restrictedFullTest (cavityProductSlice (S r) Cset) (cavityProductSlice_nonempty (S r) (hS r) Cset hCset)
    ((μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))) T
    (diagonalPerturbedEigenvalues (fun i => lam (g r i)) (cavitySpectralGroup (g r)) (v r) 1)
    (cavitySpectralGroup (g r)) (u r) (cavitySplitOverlapInsertion Φ) ∂θ r
  let scalar := fun r => ∫ t, Φ (cavityStrictUniformPath p r t) ∂pathMeasure
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hjO,hjF⟩ := ((horig (ε/2) (by positivity)).and
    (hfinite (ε/2) (by positivity))).exists
  filter_upwards [hjO,hjF] with r hrO hrF
  have hrO' : |full r-cut j r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrO
  have hrF' : |cut j r-scalar r| < ε/2 := by
    dsimp only [cut]
    rw [hA]
    exact hrF
  rw [Real.dist_eq,sub_zero]
  exact (abs_sub_le (full r) (cut j r) (scalar r)).trans_lt (by linarith)

end InvariantIsing

end

end OAI
