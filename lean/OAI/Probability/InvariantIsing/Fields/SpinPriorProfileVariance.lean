import OAI.Probability.InvariantIsing.Fields.SpinPriorHaarVariance

namespace OAI

/-! Full Haar/cascade/Gaussian concentration in the independent namespaces
used by the actual perturbation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

theorem spinPriorProfileLog_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ π : Measure (Spin N), IsProbabilityMeasure π →
    ∀ m k n : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ, ∀ amp : Fin k → ℝ,
    ∀ b : ℕ → ℝ, CascadeExponents n b → ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      let F := spinPriorProfileLog π eig c I degree amp (fun i => v i)
      let L := K*N+2*(∑ i : Fin (n+1), ∑ j, (monomial i j : ℝ)*amp j^2*∑ a, (degree j a : ℝ))
      MemLp F 2 P ∧ variance F P ≤
        4*(∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)))+
          (site 0 : ℝ)*N+∑ j, (monomial 0 j : ℝ)*amp j^2+C*L^2/N := by
  obtain ⟨C,hC,hvar⟩ := spinPriorJointFlatLog_variance hhaar hgauss
  refine ⟨C,hC,?_⟩
  intro N hN μ hμ hμinv π hπ m k n eig c K hK heig I degree amp b hb site monomial v P F L
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure π := hπ
  have hv := hvar N hN μ hμ hμinv π hπ m k n eig c K hK heig I degree amp b hb site monomial
  have hlaw := spinPriorProfileLog_law (n := n) μ π eig c I degree amp b (fun i => v i)
  have hid : MemLp id 2 (P.map (spinPriorJointFlatLog π eig c I degree amp (fun i => v i))) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hv.1.aemeasurable).mpr hv.1
  exact ⟨hlaw.memLp hid, (hlaw.variance_eq.trans (variance_id_map hv.1.aemeasurable)).trans_le hv.2⟩

end InvariantIsing

end

end OAI
