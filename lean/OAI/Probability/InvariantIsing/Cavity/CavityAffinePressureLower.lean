import OAI.Probability.InvariantIsing.Cavity.CavityAffineMinimumLower
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Cavity.CavityTensorPressureMean
import OAI.Probability.InvariantIsing.Arrays.TensorEnvelopeLower

namespace OAI

/-! The fixed-residue rational finite-spectrum pressure lower bound. All minimizers,
subsequence limits and cavity geometry are constructed in the proof. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_affine_pressure_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant]
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ j, lam j ≤ lam a) (R : Rotation n) :
    let N := cavityAffineSize n (m*n-n+n+3) c
    let g := fun M => cavityAffineLabel (by omega : 0 < m) s c hsum M
    ∀ ε > 0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal-ε ≤
      ∫ V, rotatedPressure (fun i => lam (g (N r) i)) (matrixRotation V⁻¹)
        (fun _ => 0) ∂μ (N r) := by
  intro N g
  let ν := cavityOrientedFamily μ
  let eig := fun M i => lam (g M i)
  let I := fun M => cavitySpectralGroup (g M)
  let L := (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
    (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal
  have hν M : (ν M).IsMulLeftInvariant := cavityOrientedFamily_leftInvariant μ M
  have hN r : 3 ≤ N r := cavityAffineSize_ge_three n (m*n-n) c r hn
  have hpos r : 0 < N r := by have := hN r; omega
  obtain ⟨u,v,hu,hv,hmin⟩ := tensor_zero_field_minimizing_sequence hhaar hgauss
    m depth b hb ν hν eig (fun _ _ => 0) I
  have hinc := cavity_affine_minimum_lower hhaar hgauss hpub hm hn s c hs hsum
    depth b hb μ lam a ha R (fun r => u (N r)) (fun r => v (N r))
    (fun r => hu (N r)) (fun r => hv (N r)) (by
      intro r u' v' hu' hv'
      simpa only [ν,cavityOrientedFamily_pos μ (hpos r)] using
        hmin (N r) (hN r) u' v' hu' hv')
  let N₀ := (m*n-n+n+3)*n+∑ a, c a
  have hN₀ : 3 ≤ N₀ := by simpa only [N, cavityAffineSize, zero_add] using hN 0
  have hindex r : N₀+n*r=N r := by
    dsimp only [N₀,N,cavityAffineSize]
    ring
  have hh := tensor_envelope_pressure_lower hhaar hgauss m depth N₀ n hN₀ hn
    b hb ν hν eig (fun _ _ => 0) I u v hu hv hmin L (by
      intro ε hε
      filter_upwards [hinc ε hε] with r hr
      dsimp only
      rw [hindex]
      have hf := cavity_tensor_pressure_mean (by have := hpos r; omega : 0 < N r+n)
        (μ (N r+n)) (eig (N r+n)) (I (N r+n)) (cavityBaseAmplitude (u (N r)))
        (v (N r)) 1 b hb
      have hb' := cavity_tensor_pressure_mean (hpos r) (μ (N r)) (eig (N r)) (I (N r))
        (cavityBaseAmplitude (u (N r))) (v (N r)) 1 b hb
      rw [cavityBaseAmplitude_restrict] at hb'
      rw [← cavityOrientedFamily_pos μ (by have := hpos r; omega)] at hf
      rw [← cavityOrientedFamily_pos μ (hpos r)] at hb'
      change L-(n : ℝ)⁻¹*((∫ z, cavityRotationLogMean z.2
        (diagonalPerturbedEigenvalues (eig (N r+n)) (I (N r+n)) (v (N r)) 1)
        (I (N r+n)) (cavityBaseAmplitude (u (N r))) z.1
          ∂(μ (N r+n)).prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) -
        ∫ z, cavityRotationLogMean z.2
          (diagonalPerturbedEigenvalues (eig (N r)) (I (N r)) (v (N r)) 1)
          (I (N r)) (cavityBaseAmplitude (u (N r))) z.1
            ∂(μ (N r)).prod (labeledCascadeLaw depth b : Measure (LabeledTree depth))) < ε at hr
      rw [hf,hb'] at hr
      simp only [Nat.cast_add] at hr
      change L-ε ≤ _
      rw [div_eq_mul_inv]
      linarith)
  intro ε hε
  filter_upwards [hh ε hε] with r hr
  rw [hindex] at hr
  dsimp only [ν] at hr
  rw [cavityOrientedFamily_pos μ (hpos r), cavity_oriented_pressure] at hr
  exact hr

end InvariantIsing

end

end OAI
