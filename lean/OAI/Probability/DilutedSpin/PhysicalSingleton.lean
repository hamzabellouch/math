import OAI.Probability.DilutedSpin.ActualNegligible
import OAI.Probability.DilutedSpin.CompleteShapeSelection
import OAI.Probability.DilutedSpin.PhysicalPairEnergy

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

/-- The manuscript's singleton conditional spatial covariance density, under
the actual tilted reservoir, averaged over roots and the d-coordinate prefix. -/
noncomputable def physicalSingletonEnergy (m : Fin (L+1) → ℝ) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) : ℝ :=
  ∫ z, rootConditionalEnergy
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i => prior i.1.1) m (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) d
    (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z
    ∂fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N)

noncomputable def singletonOldTest (d : ℕ) (hd : d < L+1) (N : ℕ) :
    ((forkAt (L+1) d hd).Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ :=
  pairOverlap (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0) (forkAtLeaf (L+1) d hd 1)
    (fun v x => readSpin (KernelTower.terminalState L x) v)

lemma singletonOldTest_bound (d : ℕ) (hd : d < L+1) (N : ℕ) (x) :
    |singletonOldTest d hd N x| ≤ 1 := pairOverlap_bound _ _ _ _ _

/-- Exact one-color singleton estimate at every N, before taking any limit.
The error is the literal physical prescribed-shape covariance already selected
by the universal perturbation, not a newly imposed covariance hypothesis. -/
theorem physical_singleton_bound (m : Fin (L+1) → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : Spec L×ℕ → ℝ) (d : ℕ) (hd : d < L+1) :
    (2*(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩) *
      physicalSingletonEnergy m M C H N u d ≤
    ((Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d+1,by omega⟩-(Fin.cons 0 m : Fin (L+2) → ℝ) ⟨d,by omega⟩) +
      physicalShapeCovariance m (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
        M C H N u (pairSplitTest d) true (singletonOldTest d hd N) := by
  have h := shape_energy_bound (forkAt (L+1) d hd) (forkAtLeaf (L+1) d hd 0)
    (forkAtLeaf (L+1) d hd 1)
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (fun v x => readSpin (KernelTower.terminalState L x) v) d
    (measurable_physicalBase M C H N)
    (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw (weights L) N)
    (M.alpha*N) (scoreRate N) hd (forkAt_split (L+1) d hd 0 1 (by decide))
    (forkAtVertex (L+1) d hd) (forkAt_fresh (L+1) d hd 0) (forkAt_fresh (L+1) d hd 1)
    (fun c hc => forkAt_unique (L+1) d hd c hc)
    (exponent_cons_monotone m hm hmono) (exponent_cons_nonneg m hm) (by simpa using hend)
  rw [forkAt_gamma] at h
  simp only [neg_sub] at h
  exact h

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
