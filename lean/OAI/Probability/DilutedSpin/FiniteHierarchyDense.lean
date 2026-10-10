import OAI.Probability.DilutedSpin.QSubtreePotential

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

lemma atomicProbability_reindex {X ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : ι → X) (w : AtomicWeights ι) :
    atomicProbability (fun j => x (e.symm j))
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩ =
      atomicProbability x w := by
  apply Subtype.ext
  change (∑ j : κ,(w.val (e.symm j):ℝ≥0∞) • Measure.dirac (x (e.symm j))) = _
  exact e.symm.sum_comp (fun i => (w.val i:ℝ≥0∞) • Measure.dirac (x i))

lemma continuous_atomicProbability_atoms {X ι : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T1Space X] [Fintype ι] (w : AtomicWeights ι) :
    Continuous (fun x : ι → X => atomicProbability x w) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_atomicProbability]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (f.continuous.comp (continuous_apply i)))

/-- Finite laws supported on any dense set are weakly dense. -/
lemma finite_atomic_dense {X : Type} [MetricSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (D : Set X) (hD : Dense D) :
    Dense {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w} := by
  classical
  let S := {μ : ProbabilityMeasure X | ∃ (n : ℕ) (x : Fin n → X) (w : AtomicWeights (Fin n)),
      (∀ i,x i ∈ D) ∧ μ = atomicProbability x w}
  have ha (ι : Type) [Fintype ι] (x : ι → X) (w : AtomicWeights ι) :
      atomicProbability x w ∈ closure S := by
    have hd : Dense (Set.univ.pi (fun _ : ι => D)) := dense_pi Set.univ (fun _ _ => hD)
    obtain ⟨z,hz,ht⟩ := mem_closure_iff_seq_limit.mp (hd x)
    apply isClosed_closure.mem_of_tendsto ((continuous_atomicProbability_atoms w).tendsto x |>.comp ht)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι,fun j => z n (e.symm j),
      ⟨fun j => w.val (e.symm j),by rw [e.symm.sum_comp w.val]; exact w.property⟩,?_,?_⟩
    · intro j
      exact hz n (e.symm j) (Set.mem_univ _)
    · exact (atomicProbability_reindex e (z n) w).symm
  intro μ
  let h : StronglyMeasurable (id : X → X) := stronglyMeasurable_id
  apply isClosed_closure.mem_of_tendsto (probability_map_tendsto μ h.approx h.tendsto_approx)
  apply Eventually.of_forall
  intro n
  obtain ⟨w,hw⟩ := simple_map_atomic (h.approx n) μ
  rw [← hw]
  exact ha _ _ w

local instance finiteHierarchyDenseMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance finiteHierarchyDenseBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

/-- Genuine finitely branching laws at every level, not an altered trial class. -/
def FiniteHierarchy : (r : ℕ) → Hierarchy r → Prop
  | 0,_ => True
  | r+1,μ => ∃ (n : ℕ) (x : Fin n → Hierarchy r) (w : AtomicWeights (Fin n)),
      (∀ i,FiniteHierarchy r (x i)) ∧ μ = atomicProbability x w

lemma finiteHierarchy_dense (r : ℕ) : Dense {ζ : Hierarchy r | FiniteHierarchy r ζ} := by
  induction r with
  | zero => simpa only [FiniteHierarchy,Set.ofPred_true] using (dense_univ : Dense (Set.univ : Set (Hierarchy 0)))
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    let : SeparableSpace (Hierarchy r) := (hierarchy_properties r).2
    exact finite_atomic_dense {ζ : Hierarchy r | FiniteHierarchy r ζ} ih

end DilutedSpinGlass

end

end OAI
