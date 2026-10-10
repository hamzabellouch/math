import OAI.Probability.InvariantIsing.Cavity.CavityOriginalFullSpin
import OAI.Probability.InvariantIsing.Cavity.CavityOverlapWeightedTest
import OAI.Probability.InvariantIsing.Cavity.CavityFieldModulus

namespace OAI

/-! Cavity self-consistency for the actual original-model spin law,
conditional on the published inputs and the proved geometric/GG limit data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction BigOperators

namespace InvariantIsing

theorem cavity_original_scalar_self_consistency (hpub : PanchenkoTalagrandFieldPairInput) {m d n : ℕ}
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
    :
    let p := spectralSpinQuantilePath Q₀ hP hnonneg
    Tendsto (fun r => ∫ s,
      |fieldMagnetizationPath (cavityStrictUniformField ρ lam hρ hρsum p r) s-p s| ∂pathMeasure)
      atTop (𝓝 0) := by
  intro p
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hKl a : |lam a| ≤ K := Finset.single_le_sum (fun b _ => abs_nonneg (lam b)) (Finset.mem_univ a)
  apply cavity_strict_field_self_consistency ρ lam hρ hρsum hK hKl p
  intro Φ
  let site : Fin n := ⟨0,hn⟩
  let Ψ := cavityOverlapWeightedTest Φ
  let μO := fun r => (μ r).map (cavityOrientationLift (Nat.add_pos_left (hN r) n))
  let (r : ℕ) : IsProbabilityMeasure (μO r) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_cavityOrientationLift _).aemeasurable).mpr inferInstance
  let (r : ℕ) : (μO r).IsMulRightInvariant := cavityOrientationLift_measure_rightInvariant _ _
  let eig := fun r => diagonalPerturbedEigenvalues (fun i => lam (g r i))
    (cavitySpectralGroup (g r)) (v r) 1
  let q := cavityStrictUniformPath p
  let f := fun r => fieldMagnetizationPath (cavityStrictUniformField ρ lam hρ hρsum p r)
  let G := fun r => ∫ T, cavityFullTest (μO r) T (eig r) (cavitySpectralGroup (g r)) (u r)
    (cavityFullSpinInsertion Φ (Fin.natAdd (N r) site)) ∂θ r
  let A := fun r => ∫ t, Φ (q r t) * f r t ∂pathMeasure
  let C := fun r => ∫ t, Φ (q r t) * q r t ∂pathMeasure
  have hspin := cavity_original_spin_limit hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a ha Φ site
  have hs : Tendsto (fun r => G r-A r) atTop (𝓝 0) := hspin
  have hoverlap := cavity_original_overlap_limit hpub N depth hN hNlim g k ek e es B₀ a₀ hk μG
    l w hg hln hw μ ν θ lam v hv u hu good hgood hp hL hbound hd hn hB₀ ρ hρ hρsum hperp
    hgroups hdims hc hcG hρlim A_ hA hprob Q₀ hlim hgg hG δ hδ0 hδ hE hP hnonneg hoff hdiag
    a ha Ψ
  have ho : Tendsto (fun r => G r-C r) atTop (𝓝 0) := by
    convert hoverlap using 1
    funext r
    have hsite := cavity_full_weighted_overlap_identity (Nat.add_pos_left (hN r) n)
      (μO r) (θ r) (eig r) (cavitySpectralGroup (g r)) (u r) (hu r) Φ (Fin.natAdd (N r) site)
    have hlevel : (∫ t, Ψ (q r t) ∂pathMeasure) = C r := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact cavityOverlapWeightedTest_eq Φ ⟨by linarith [(q r).nonneg t],(q r).le_one t⟩
    change G r-C r = _ - _
    rw [← hsite,hlevel]
  have hh := ho.sub hs
  simp only [sub_zero] at hh
  convert hh using 1
  funext r
  have hi (v : OverlapPath) : Integrable (fun t => Φ (q r t)*v t) pathMeasure := by
    apply integrable_of_measurable_abs_le
      ((Φ.continuous.measurable.comp (q r).measurable).mul v.measurable)
    intro t
    change |Φ (q r t)*v t| ≤ ‖Φ‖
    rw [abs_mul,abs_of_nonneg (v.nonneg t)]
    exact (mul_le_mul_of_nonneg_left (v.le_one t) (abs_nonneg _)).trans
      (by simpa only [mul_one,Real.norm_eq_abs] using Φ.norm_coe_le_norm (q r t))
  change (∫ t, Φ (q r t)*(f r t-q r t) ∂pathMeasure) = (G r-C r)-(G r-A r)
  simp_rw [mul_sub]
  rw [integral_sub (hi (f r)) (hi (q r))]
  dsimp only [A,C]
  ring

end InvariantIsing

end

end OAI
