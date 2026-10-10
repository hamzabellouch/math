import OAI.Probability.InvariantIsing.Cavity.CavityAffinePressureLower
import OAI.Probability.InvariantIsing.Core.FiniteSpectrumVariationalUpper

namespace OAI

/-! Exact limiting pressure for rational finite spectra along each
fixed residue progression. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ) :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
    Tendsto (fun r => ∫ V, rotatedPressure (fun i => lam (g (N r) i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (N r)) atTop
      (𝓝 (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal) := by
  intro N g
  have hm0 : 0 < m := by omega
  let q := m*n-n+n+3
  let ρ := fun a => (s a : ℝ)/n
  let eig := fun r i => lam (g (N r) i)
  let I := fun r => cavitySpectralGroup (g (N r))
  let L := (variationalFunctional (finiteR ρ lam
    (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ lam
    ⟨⟨0,hm0⟩,Finset.mem_univ _⟩
  have hb : CascadeExponents 0 (fun _ => 0) := by
    constructor <;> intro i hi <;> omega
  have hlo := cavity_affine_pressure_lower hhaar hgauss hpub hm hn s c hs hsum
    0 (fun _ => 0) hb μ lam a (fun j => ha j (Finset.mem_univ j))
    (LinearIsometryEquiv.refl ℝ _)
  have hpos r : 0 < N r := by
    change 0 < cavityAffineSize n (m*n-n+n+3) c r
    have := cavityAffineSize_ge_three n (m*n-n) c r hn
    omega
  let ν := fun r => cavityOrientedBaseLaw (hpos r) (μ (N r))
  have hcard r a : (I r a).card=cavityAffineCount s c q r a := by
    change (cavitySpectralGroup (cavityAffineLabel hm0 s c hsum (cavityAffineSize n q c r)) a).card=_
    rw [cavityAffineLabel_progression hm0 s c hsum hn]
    exact cavityOrderedGroup_card _ _ a
  have hmass : Tendsto (fun r a => ((I r a).card : ℝ)/N r) atTop (𝓝 ρ) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [hcard] using cavityAffineCount_ratio s c hn (q := q) (by omega) a
  let K := 1+∑ a, |lam a|
  have hK : 0 < K := by
    have h := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => abs_nonneg (lam a))
    dsimp only [K]
    linarith
  have hbound r i : |eig r i| ≤ K := by
    have h := Finset.single_le_sum (f := fun a => |lam a|)
      (fun a _ => abs_nonneg (lam a)) (Finset.mem_univ (g (N r) i))
    dsimp only [eig,K]
    linarith
  have hup := finiteSpectrum_meanPressure_variational_upper hhaar hgauss N
    (fun r => cavityAffineSize_ge_three n (m*n-n) c r hn)
    (cavityAffineSize_tendsto n q c hn) m ν
    (fun r => cavityOrientedBaseLaw_leftInvariant (hpos r) (μ (N r))) eig K hK hbound I
    (fun r => cavitySpectralGroup_pairwiseDisjoint _) (fun r => cavitySpectralGroup_cover _)
    lam (by intro r a i hi; change lam (g (N r) i)=lam a; rw [(Finset.mem_filter.mp hi).2])
    ρ (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn) hmass
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlo (ε/2) (half_pos hε),hup (ε/2) (half_pos hε)] with r hl hu
  rw [cavity_oriented_pressure] at hu
  change dist _ L < ε
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end InvariantIsing

end

end OAI
