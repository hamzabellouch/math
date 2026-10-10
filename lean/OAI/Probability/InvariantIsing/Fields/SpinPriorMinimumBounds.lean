import OAI.Probability.InvariantIsing.Fields.SpinPriorGGMinimum
import OAI.Probability.InvariantIsing.Fields.SpinPriorMinimumCoordinates
import OAI.Probability.InvariantIsing.Fields.SpinPriorPerturbationVariance

namespace OAI

/-! Actual constrained-prior minima satisfy both uniform perturbation bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorPerturbation_minimum_bounds (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 3≤N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m n : ℕ, ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0<K → (∀ i, |eig i|≤K) →
    ∀ I : Fin m → Finset (Fin N), ∀ u : Fin N → ℝ, (∀ j, u j∈Set.Icc (1 : ℝ) 2) →
    ∀ v : Fin m → ℝ, (∀ a, v a∈Set.Icc (1 : ℝ) 2) → ∀ t : ℝ, |t|≤1 →
    ∀ h : ℕ → ℝ, Monotone h → 0≤h 0 → ∀ H : ℝ, h n≤H →
      let d := fun j : Fin N => enumeratedSpectralDegree m j
      let r := fun j : Fin N => enumeratedTreeDegree m j
      let L := 4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2
        ∂(rawCascadeLaw n b : Measure (RawTree n)))+H+4+C*(K+4*m+8)^2
      perturbationScale N≤1/32 → contactStep N≤1/4 →
      (∀ u' v', (∀ j, u' j∈Set.Icc (1 : ℝ) 2) → (∀ a, v' a∈Set.Icc (1 : ℝ) 2) →
        spinPriorPerturbationObjective (n := n) μ π eig c I b t h u v≤ spinPriorPerturbationObjective (n := n) μ π eig c I b t h u' v') →
      (∀ a, spinPriorObservableAverage (n := n) μ π (diagonalPerturbedEigenvalues eig I v t)
        c I d (tensorPerturbationAmplitude N u) b r h
        (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-diagonalMinimumCenter N (v a)|)
          ≤diagonalContactRate N L) ∧
      (∀ j : Fin N, ∀ q : ℕ, ∀ B : ℝ, 0≤B →
        ∀ D : SpecialOrthogonal N → (Fin (q+1) → Spin N × LabeledLeaf n) → ℝ,
        Measurable (Function.uncurry D) → (∀ U σ, |D U σ|≤B) →
        |spinPriorSpectralGGResidual μ π b (diagonalPerturbedEigenvalues eig I v t)
          c I d (tensorPerturbationAmplitude N u) r h j D|≤
          contactGGRate N j L B+2*B*(∑ a, (d j a : ℝ))*diagonalContactRate N L) := by
  obtain ⟨C,hC,hvar⟩ := spinPriorPerturbation_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hu v hv t ht h hh h0 H hH d r L he hs hmin
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  have hNp : 0<N := by omega
  have hua : ∀ j, |u j|≤2 := fun j => abs_le.mpr ⟨by linarith [(hu j).1],(hu j).2⟩
  have hva : ∀ a, |v a|≤2 := fun a => abs_le.mpr ⟨by linarith [(hv a).1],(hv a).2⟩
  let amplitude := tensorPerturbationAmplitude N u
  have hcoords := spinPriorPerturbation_minimum_coordinates (n := n) μ π b eig c I t h u v hu hv hmin
  have hgv (a : Fin m) (w : ℝ) (hw : |w|≤2) :
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I d amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I d amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L := by
    exact hvar N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I u hua
      (Function.update v a w) (update_abs_le_two hva a hw) t ht h hh h0 H hH
  have hdiag (a : Fin m) : spinPriorObservableAverage (n := n) μ π
      (diagonalPerturbedEigenvalues eig I v t) c I d amplitude b r h
      (fun U x => |projectedOverlap (specialRotation U) (I a) x.1 x.1-diagonalMinimumCenter N (v a)|)
        ≤diagonalContactRate N L := by
    have hd := spinPriorDiagonal_fluctuation_at_minimum hNp μ π b eig c I d amplitude r h hh h0
      v t a (v a) L (hv a) he hs (fun w hw => (hgv a w hw).1) (fun w hw => (hgv a w hw).2) (by
        dsimp only
        intro w hw
        simpa only [spinPriorPerturbationPressureMean_eq_namespaced,Function.update_eq_self]
          using hcoords.2 a w hw)
    simpa only [Function.update_eq_self,diagonalMinimumCenter] using hd
  refine ⟨hdiag,?_⟩
  intro j q B hB D hD hDb
  have hgu (w : ℝ) (hw : |w|≤2) :
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I d
        (Function.update amplitude j (perturbationAmplitude N j*w))
        r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t) c I d
        (Function.update amplitude j (perturbationAmplitude N j*w))
        r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤N*L := by
    have hx := hvar N hN μ hμ hμinv m n π hπ b hb eig c K hK heig I (Function.update u j w)
      (update_abs_le_two hua j hw) v hva t ht h hh h0 H hH
    change MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
      c I d (tensorPerturbationAmplitude N (Function.update u j w)) r h) 2
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ∧
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
        c I d (tensorPerturbationAmplitude N (Function.update u j w)) r h)
        ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates) ≤ N*L at hx
    simpa only [tensorPerturbationAmplitude_update] using hx

  have hgm :
      let M := fun w => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I v t)
        c I d (Function.update amplitude j (perturbationAmplitude N j*w))
        r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ w∈Set.Icc (1 : ℝ) 2,
        -M (u j)+perturbationWeight j*(u j-3/2)^2≤-M w+perturbationWeight j*(w-3/2)^2 := by
    dsimp only
    intro w hw
    simpa only [amplitude,spinPriorPerturbationPressureMean_eq_namespaced,← tensorPerturbationAmplitude_update,
      Function.update_eq_self] using hcoords.1 j w hw
  have hg := spinPriorGaussianGG_at_minimum hNp μ π b (diagonalPerturbedEigenvalues eig I v t)
    c I d amplitude r h hh h0 j (u j) L (hu j) (by linarith) hs rfl
    (fun w hw => (hgu w hw).1) (fun w hw => (hgu w hw).2) hgm B hB D hD hDb
    (fun a => diagonalMinimumCenter N (v a)) (fun _ => diagonalContactRate N L) hdiag
  simpa only [← Finset.sum_mul,mul_assoc] using hg

end InvariantIsing

end

end OAI
