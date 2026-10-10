import Mathlib

namespace OAI

namespace Problem367

open MeasureTheory

theorem measurableSet_isChain {Ω V : Type*} [MeasurableSpace Ω]
    {R : Ω → V → V → Prop}
    (hR : ∀ u v, MeasurableSet {ω | R ω u v}) (l : List V) :
    MeasurableSet {ω | List.IsChain (R ω) l} := by
  induction l with
  | nil => simp
  | cons u l ih =>
      cases l with
      | nil => simp
      | cons v l =>
          simpa only [List.isChain_cons_cons, Set.ofPred_and] using (hR u v).inter ih

theorem measurableSet_reflTransGen {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {R : Ω → V → V → Prop}
    (hR : ∀ u v, MeasurableSet {ω | R ω u v}) (u v : V) :
    MeasurableSet {ω | Relation.ReflTransGen (R ω) u v} := by
  classical
  have heq : {ω | Relation.ReflTransGen (R ω) u v} =
      ⋃ l : List V, {ω | List.IsChain (R ω) (u :: l) ∧
        (u :: l).getLast (List.cons_ne_nil _ _) = v} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hend⟩ => List.relationReflTransGen_of_exists_isChain_cons l hl hend⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  by_cases hend : (u :: l).getLast (List.cons_ne_nil _ _) = v
  · simpa only [hend, and_true] using measurableSet_isChain hR (u :: l)
  · simp only [hend, and_false, Set.ofPred_false]
    exact MeasurableSet.empty

theorem reflTransGen_equiv_iff {V W : Type*} (e : V ≃ W)
    {R : V → V → Prop} {S : W → W → Prop}
    (hRS : ∀ u v, S (e u) (e v) ↔ R u v) (u v : V) :
    Relation.ReflTransGen S (e u) (e v) ↔ Relation.ReflTransGen R u v := by
  constructor
  · intro h
    have hback := Relation.ReflTransGen.lift e.symm (p := R)
      (fun x y hxy => (hRS (e.symm x) (e.symm y)).mp
        (by simpa only [Equiv.apply_symm_apply] using hxy)) (e u) (e v) h
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hback
  · intro h
    exact Relation.ReflTransGen.lift e (p := S)
      (fun x y hxy => (hRS x y).mpr hxy) u v h

theorem measurable_reachableSet {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {R : Ω → V → V → Prop}
    (hR : ∀ u v, MeasurableSet {ω | R ω u v}) (u : V) :
    Measurable (fun ω => {v | Relation.ReflTransGen (R ω) u v}) := by
  apply measurable_set_iff.mpr
  intro v
  exact measurableSet_setOfPred.mp (measurableSet_reflTransGen hR u v)

theorem measurableSet_finite_reachable {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {R : Ω → V → V → Prop}
    (hR : ∀ u v, MeasurableSet {ω | R ω u v}) (u : V) :
    MeasurableSet {ω | Set.Finite {v | Relation.ReflTransGen (R ω) u v}} :=
  MeasurableSet.setOfPred_finite.preimage (measurable_reachableSet hR u)

theorem measurableSet_all_finite_reachable {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    {R : Ω → V → V → Prop}
    (hR : ∀ u v, MeasurableSet {ω | R ω u v}) :
    MeasurableSet {ω | ∀ u, Set.Finite {v | Relation.ReflTransGen (R ω) u v}} := by
  simpa only [Set.ofPred_forall] using
    MeasurableSet.iInter (fun u => measurableSet_finite_reachable hR u)

end Problem367

end OAI
