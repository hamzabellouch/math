import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.Refinement

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma through_snoc_castSucc {N t : ℕ} (w : History N t) (v : Fin N) (i : Fin t) :
    through (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) i.castSucc = through w i := by
  funext j
  change Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v
    (Fin.castSucc ⟨j.val,Nat.lt_of_lt_of_le j.isLt i.isLt⟩) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (t+1) => Fin N) v w ⟨j.val,Nat.lt_of_lt_of_le j.isLt i.isLt⟩

lemma through_last {N t : ℕ} (w : History N (t+1)) : through w (Fin.last t) = w := by
  funext j
  rfl

instance AnalysisState.indexMeasurableSpace {n : ℕ} (s : AnalysisState n) : MeasurableSpace s.Index := ⊤

instance AnalysisState.indexMeasurableSingleton {n : ℕ} (s : AnalysisState n) : MeasurableSingletonClass s.Index := ⟨fun _ => trivial⟩

structure Realization {n N t : ℕ} (s : AnalysisState n) (f : s.Index → History N t) where
  Q : Disclosure n N t
  Qmeas : ∀ i, Measurable (fun zh : Coordinate n × History N (i.val+1) => Q i zh.1 zh.2)
  Qfinite : ∀ i, (Set.range (fun zh : Coordinate n × History N (i.val+1) => Q i zh.1 zh.2)).Finite
  read : Coordinate n → History N t → s.Index
  read_meas : Measurable (fun zw : Coordinate n × History N t => read zw.1 zw.2)
  erase_read : ∀ z w, f (read z w) = w
  chosen : ∀ j z, 0 < s.channel.prob j z → read z (f j) = j
  trace : s.Index → Fin t → Cell n
  trace_read : ∀ z w i, trace (read z w) i = Q i z (through w i)
  trace_cube : ∀ j i, cellSet (trace j i) ⊆ initialCube n
  trace_below : ∀ j i, cellSet (s.cell j) ⊆ cellSet (trace j i)
  trace_nested : ∀ k (i j : Fin t), i ≤ j → cellSet (trace k j) ⊆ cellSet (trace k i)
  cell_cube : ∀ j, cellSet (s.cell j) ⊆ initialCube n
  read_mem : ∀ z ∈ initialCube n, ∀ w, z ∈ cellSet (s.cell (read z w))
  depth_read : ∀ z w, finalLevel Q (z,w) = (s.cell (read z w)).1

lemma Realization.valid {n N t : ℕ} {s : AnalysisState n} {f : s.Index → History N t}
    (R : Realization s f) : ValidDisclosure R.Q := by
  refine ⟨R.Qmeas,R.Qfinite,?_,?_⟩
  · intro z hz w i
    rw [← R.trace_read]
    exact ⟨R.trace_below (R.read z w) i (R.read_mem z hz w),R.trace_cube _ i⟩
  · intro z hz w i j hij
    rw [← R.trace_read,← R.trace_read]
    exact R.trace_nested _ i j hij

noncomputable def initialRealization {n N : ℕ} (hn : 0 < n) :
    Realization (initialState hn) (fun _ => (Fin.elim0 : History N 0)) where
  Q := fun i => Fin.elim0 i
  Qmeas := fun i => Fin.elim0 i
  Qfinite := fun i => Fin.elim0 i
  read := fun _ _ => ()
  read_meas := measurable_const
  erase_read := fun _ _ => Subsingleton.elim _ _
  chosen := fun j _ _ => by change () = (j : Unit); exact Subsingleton.elim _ _
  trace := fun _ i => Fin.elim0 i
  trace_read := fun _ _ i => Fin.elim0 i
  trace_cube := fun _ i => Fin.elim0 i
  trace_below := fun _ i => Fin.elim0 i
  trace_nested := fun _ i => Fin.elim0 i
  cell_cube := fun _ => by change cellSet (rootCell n) ⊆ initialCube n; rw [cellSet_root]
  read_mem := fun z hz _ => by change z ∈ cellSet (rootCell n); rwa [cellSet_root]
  depth_read := fun _ _ => by simp [finalLevel,initialState,rootCell]

lemma ExtensionWitness.choose_meas {n N : ℕ} {s s' : AnalysisState n}
    {q : s.Index → FiniteChannel (Coordinate n) (Fin N)} {g : s'.Index → s.Index × Fin N}
    (E : ExtensionWitness s q s' g) : Measurable (fun iz : (s.Index × Fin N) × Coordinate n => E.choose iz.1 iz.2) := by
  apply measurable_from_prod_countable_right
  intro i
  apply measurable_to_countable
  intro z
  exact E.choose_fiber i (E.choose i z)

end RepeatedLocalization

end OAI
