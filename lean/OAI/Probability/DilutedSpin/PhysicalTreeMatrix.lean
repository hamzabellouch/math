import OAI.Probability.DilutedSpin.MatrixPhysical
import OAI.Probability.DilutedSpin.RootProjectionIntegrability
import OAI.Probability.DilutedSpin.ScheduledFrameGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- Literal centered history for the multileaf old overlap, with the actual
variable-marker root alphabet. -/
noncomputable def physicalTreeMatrixCovariance (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) : ℝ :=
  matrixRootCovariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) m (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (Fin.cons 0 m) (List.ofFn (fun j : Fin k => (some j : Option (Fin k)))).reverse a
    (fun z => spatialProduct (fun _ => rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
    (fun z => treeOverlap S (rootVector
      (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))

lemma physicalTreeMatrixCovariance_eq (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin k) → T.Leaf) :
    physicalTreeMatrixCovariance m S a M C H N u T q =
      physicalMatrixCovariance m S a M C H N u T q
        (spatialProduct (fun _ : S.Leaf =>
          readVector (fun v x => readSpin (KernelTower.terminalState L x) v))) := by
  unfold physicalTreeMatrixCovariance physicalMatrixCovariance
  congr 1
  funext z x
  rw [treeOverlap_eq_spatialProduct]
  rfl

/-- The canonical insertion history really has the precise head/tail
required by the integrated proper-child inequality. -/
lemma physicalTreeMatrixCovariance_history (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin (k+1)) → T.Leaf) :
    physicalTreeMatrixCovariance m S a M C H N u T q =
      matrixRootCovariance
        (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
        (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
          (fun i => prior i.1.1) m (physicalBase M C H N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
        (Fin.cons 0 m) (some (Fin.last k)::canonicalMatrixTail k) a
        (fun z => spatialProduct (fun _ => rootVector
          (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
        (fun z => treeOverlap S (rootVector
          (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z)) := by
  unfold physicalTreeMatrixCovariance
  rw [canonicalMatrixHistory]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
