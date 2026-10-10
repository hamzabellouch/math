import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.Realization

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

lemma through_init {N t : ℕ} (w : History N (t+1)) (i : Fin t) :
    through (Fin.init w) i = through w i.castSucc := by
  funext j
  rfl

noncomputable def extendRealization {n N t : ℕ} {s s' : AnalysisState n}
    {f : s.Index → History N t} {q : s.Index → FiniteChannel (Coordinate n) (Fin N)}
    {g : s'.Index → s.Index × Fin N} (R : Realization s f) (E : ExtensionWitness s q s' g) :
    Realization s' (fun j => Fin.snoc (α := fun _ : Fin (t+1) => Fin N) (f (g j).1) (g j).2) := by
  classical
  let rd := fun (z : Coordinate n) (w : History N (t+1)) => E.choose (R.read z (Fin.init w),w (Fin.last t)) z
  have hrd : Measurable (fun zw : Coordinate n × History N (t+1) => rd zw.1 zw.2) := by
    apply E.choose_meas.comp (f := fun zw : Coordinate n × History N (t+1) => ((R.read zw.1 (Fin.init zw.2),zw.2 (Fin.last t)),zw.1))
    exact ((R.read_meas.comp (measurable_fst.prodMk ((measurable_of_countable (fun w : History N (t+1) => Fin.init w)).comp measurable_snd))).prodMk
      ((measurable_of_countable (fun w : History N (t+1) => w (Fin.last t))).comp measurable_snd)).prodMk measurable_fst
  have herase (z : Coordinate n) (w : History N (t+1)) :
      g (rd z w) = (R.read z (Fin.init w),w (Fin.last t)) := E.erase_choose _ _
  let Q : Disclosure n N (t+1) := Fin.lastCases (fun z w => s'.cell (rd z w)) R.Q
  let tr : s'.Index → Fin (t+1) → Cell n := fun j => Fin.snoc (R.trace (g j).1) (s'.cell j)
  refine {
    Q := Q
    Qmeas := ?_
    Qfinite := ?_
    read := rd
    read_meas := hrd
    erase_read := ?_
    chosen := ?_
    trace := tr
    trace_read := ?_
    trace_cube := ?_
    trace_below := ?_
    trace_nested := ?_
    cell_cube := fun j => (E.subset j).trans (R.cell_cube (g j).1)
    read_mem := ?_
    depth_read := ?_ }
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Q,Fin.lastCases_last]
      change Measurable (fun zw : Coordinate n × History N (t+1) => s'.cell (rd zw.1 zw.2))
      exact (measurable_of_countable s'.cell).comp hrd
    · simp only [Q,Fin.lastCases_castSucc]
      change Measurable (fun zw : Coordinate n × History N (j.val+1) => R.Q j zw.1 zw.2)
      exact R.Qmeas j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Q,Fin.lastCases_last]
      change (Set.range (fun zw : Coordinate n × History N (t+1) => s'.cell (rd zw.1 zw.2))).Finite
      apply (Set.finite_range s'.cell).subset
      rintro c ⟨zw,rfl⟩
      exact ⟨rd zw.1 zw.2,rfl⟩
    · simp only [Q,Fin.lastCases_castSucc]
      change (Set.range (fun zh : Coordinate n × History N (j.val+1) => R.Q j zh.1 zh.2)).Finite
      exact R.Qfinite j
  · intro z w
    rw [herase,R.erase_read]
    exact Fin.snoc_init_self w
  · intro j z hz
    dsimp only [rd]
    rw [Fin.init_snoc,Fin.snoc_last,R.chosen (g j).1 z (E.positive_parent j z hz)]
    exact E.chosen j z hz
  · intro z w i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [tr,Q,through_last]
    · simp only [tr,Q,Fin.snoc_castSucc,Fin.lastCases_castSucc]
      rw [herase]
      simpa only [through_init] using R.trace_read z (Fin.init w) j
  · intro j i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [tr,Fin.snoc_last]
      exact (E.subset j).trans (R.cell_cube _)
    · simp only [tr,Fin.snoc_castSucc]
      exact R.trace_cube _ k
  · intro j i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [tr,Fin.snoc_last]
      exact Subset.rfl
    · simp only [tr,Fin.snoc_castSucc]
      exact (E.subset j).trans (R.trace_below _ k)
  · intro k i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _; exact Subset.rfl
      · intro h; exact False.elim (by have := b.isLt; change t ≤ b.val at h; omega)
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _
        simp only [tr,Fin.snoc_last,Fin.snoc_castSucc]
        exact (E.subset k).trans (R.trace_below _ a)
      · intro h
        simpa only [tr,Fin.snoc_castSucc] using R.trace_nested (g k).1 a b h
  · intro z hz w
    exact E.contains _ z (R.read_mem z hz (Fin.init w))
  · intro z w
    simp only [finalLevel,show 0 < t+1 by omega,dite_eq_left]
    change (Q (Fin.last t) z (through w (Fin.last t))).1 = (s'.cell (rd z w)).1
    rw [through_last]
    simp only [Q,Fin.lastCases_last]

end RepeatedLocalization

end OAI
