import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistory
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

instance snapshotMeasurableSpace : MeasurableSpace (Snapshot I V) := ⊤

instance snapshotMeasurableSingletonClass : MeasurableSingletonClass (Snapshot I V) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

def initialSnapshot : Snapshot I V := (some initialState, none)

def snapshotPathLaw (p : Parameters) (q : ℕ) (G : Input I V) :
    Measure (FiniteHistory.Path (Snapshot I V)) :=
  FiniteHistory.pathLaw (fun t => snapshotPMF p q t G) initialSnapshot

instance snapshotPathLaw_isProbability (p : Parameters) (q : ℕ) (G : Input I V) :
    IsProbabilityMeasure (snapshotPathLaw p q G) := by
  unfold snapshotPathLaw
  infer_instance

def snapshotFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (FiniteHistory.Path (Snapshot I V))) :=
  FiniteHistory.filtration

theorem condExp_snapshot_step (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ) :
    (snapshotPathLaw p q G)[FiniteHistory.stepObservable t f | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, snapshotWeight p q t G (ω t) out * f (frestrictLe t ω) out := by
  have h := FiniteHistory.condExp_stepObservable
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t f
  simpa only [snapshotPathLaw, snapshotFiltration, snapshotPMF_apply_real] using h

theorem snapshotPathLaw_prefix (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ) :
    (snapshotPathLaw p q G).map (frestrictLe t) =
      Kernel.partialTraj (X := fun _ => Snapshot I V)
        (FiniteHistory.historyKernel (fun n => snapshotPMF p q n G)) 0 t
          (fun _ => initialSnapshot) :=
  FiniteHistory.map_prefix_pathLaw (fun n => snapshotPMF p q n G) initialSnapshot t

theorem sum_snapshotWeight_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (f : Snapshot I V → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out) =
      ∑ draw, drawStepWeight p q t G before.1 draw *
        f (advance q G before.1 draw, draw) := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem condExp_retained_draw (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Option (Noise I V) → ℝ) :
    (snapshotPathLaw p q G)[
      FiniteHistory.stepObservable t (fun h out => f h out.2) | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          f (frestrictLe t ω) draw := by
  have h := condExp_snapshot_step p q G t (fun h out => f h out.2)
  filter_upwards [h] with ω hω
  rw [hω, sum_snapshotWeight_response]

theorem sum_drawStepWeight_of_precheck (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (f : Option (Noise I V) → ℝ) :
    (∑ draw, drawStepWeight p q t G (some S) draw * f draw) =
      ∑ r : Noise I V, noiseWeight p q G S r * f (some r) := by
  simp [Fintype.sum_option, drawStepWeight, hp]

end Balanced.Selection.Process

end

end OAI
