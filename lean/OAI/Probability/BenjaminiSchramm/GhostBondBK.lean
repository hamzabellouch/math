import OAI.Probability.BenjaminiSchramm.GhostField
import OAI.Probability.BenjaminiSchramm.PeakComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V E T : Type*} (G : BondGraph V E) (x : V) (vertex : T → V)

def finiteGhostConnection (m : Set T) : Set (Set E) :=
  {ω | ∃ i ∈ m, Conn G ω x (vertex i)}

lemma finiteGhostConnection_upper (m : Set T) : IsUpperSet (finiteGhostConnection G x vertex m) := by
  rintro ω η hωη ⟨i,hi,hc⟩
  exact ⟨i,hi,conn_mono G hωη hc⟩

lemma finiteGhostConnection_finiteWitness (m : Set T) :
    FiniteWitness (finiteGhostConnection G x vertex m) := by
  rintro ω ⟨i,hi,hc⟩
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x (vertex i) ω hc
  exact ⟨s,hs,i,hi,hconn⟩

theorem finiteGhostConnection_bk [Countable E] (p : unitInterval) (m n : Set T) :
    (law p).real (DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n)) ≤
        (law p).real (finiteGhostConnection G x vertex m) *
          (law p).real (finiteGhostConnection G x vertex n) :=
  bk p _ _ (finiteGhostConnection_upper G x vertex m) (finiteGhostConnection_upper G x vertex n)
    (finiteGhostConnection_finiteWitness G x vertex m) (finiteGhostConnection_finiteWitness G x vertex n)

theorem averaged_finiteGhostConnection_bk [Fintype T] [Countable E]
    (p : unitInterval) (ν : Measure (Set T)) [IsProbabilityMeasure ν] :
    (∫ m, ∫ n, (law p).real (DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n)) ∂ν ∂ν) ≤
        (∫ m, (law p).real (finiteGhostConnection G x vertex m) ∂ν) ^ 2 := by
  calc
    _ ≤ ∫ m, ∫ n, (law p).real (finiteGhostConnection G x vertex m) *
        (law p).real (finiteGhostConnection G x vertex n) ∂ν ∂ν := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro m
      exact integral_mono Integrable.of_finite Integrable.of_finite
        (fun n => finiteGhostConnection_bk G x vertex p m n)
    _ = _ := by
      simp_rw [integral_const_mul]
      rw [integral_mul_const, sq]

lemma measurable_finiteGhostConnection_measure [Countable V] [Countable T] [Countable E]
    (p : unitInterval) : Measurable (fun m => law p (finiteGhostConnection G x vertex m)) := by
  have hm : MeasurableSet {z : Set T × Set E | ∃ i ∈ z.1, Conn G z.2 x (vertex i)} := by
    have heq : {z : Set T × Set E | ∃ i ∈ z.1, Conn G z.2 x (vertex i)} =
        ⋃ i : T, {z : Set T × Set E | i ∈ z.1} ∩ {z | Conn G z.2 x (vertex i)} := by
      ext z
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      (((measurable_set_mem i).comp measurable_fst).setOf).inter
        ((measurableSet_conn G x (vertex i)).preimage measurable_snd)
  exact measurable_measure_prodMk_left (ν := law p) hm

theorem averaged_ghostConnection_bk [Countable V] [Countable T] [Countable E]
    (p : unitInterval) (ν : Measure (Set T)) :
    (∫⁻ m, ∫⁻ n, law p (DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n)) ∂ν ∂ν) ≤
        (∫⁻ m, law p (finiteGhostConnection G x vertex m) ∂ν) ^ 2 := by
  have hm := measurable_finiteGhostConnection_measure G x vertex p
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, law p (finiteGhostConnection G x vertex m) *
        law p (finiteGhostConnection G x vertex n) ∂ν ∂ν := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact bk_ennreal p _ _
        (finiteGhostConnection_upper G x vertex m) (finiteGhostConnection_upper G x vertex n)
        (finiteGhostConnection_finiteWitness G x vertex m)
        (finiteGhostConnection_finiteWitness G x vertex n)
    _ = _ := by
      simp_rw [lintegral_const_mul _ hm]
      rw [lintegral_mul_const _ hm, sq]

lemma measurableSet_ghostDisjointOccurrence [Countable T] [Countable E] :
    MeasurableSet {z : (Set T × Set T) × Set E |
      z.2 ∈ DisjointOccurrence (finiteGhostConnection G x vertex z.1.1)
        (finiteGhostConnection G x vertex z.1.2)} := by
  have hsub (s : Finset E) :
      Measurable (fun z : (Set T × Set T) × Set E => (s : Set E) ⊆ z.2) := by
    exact Measurable.forall fun e =>
      measurable_const.imp ((measurable_set_mem e).comp measurable_snd)
  have hc (s : Finset E) (j : Fin 2) :
      Measurable (fun z : (Set T × Set T) × Set E =>
        ∃ i ∈ (if j = 0 then z.1.1 else z.1.2), Conn G (s : Set E) x (vertex i)) := by
    apply Measurable.exists
    intro i
    by_cases hj : j = 0
    · simpa only [ite_eq_left hj, Function.comp_def] using
        (((measurable_set_mem i).comp (measurable_fst.comp measurable_fst)).and
          (measurable_const : Measurable (fun _ : (Set T × Set T) × Set E =>
            Conn G (s : Set E) x (vertex i))))
    · simpa only [ite_eq_right hj, Function.comp_def] using
        (((measurable_set_mem i).comp (measurable_snd.comp measurable_fst)).and
          (measurable_const : Measurable (fun _ : (Set T × Set T) × Set E =>
            Conn G (s : Set E) x (vertex i))))
  exact (Measurable.exists fun s : Finset E => Measurable.exists fun t : Finset E =>
    (hsub s).and ((hsub t).and (measurable_const.and ((hc s 0).and (hc t 1))))).setOf

end Percolation.BenjaminiSchramm

end

end OAI
