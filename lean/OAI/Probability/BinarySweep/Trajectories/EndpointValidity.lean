import Mathlib
import OAI.Probability.BinarySweep.Trajectories.EndpointEvents

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}

lemma gridPartialSweep_endpoint (g : GridChoices bits) (e : GridSlot bits × GridSlot bits)
    (he : gridSweep bits g e.1=e.2) (t : Fin (b+1)) :
    gridPartialSweep bits g t e.1=independentPosition e t := by
  have hh := independentPosition_of_path (fun t => gridPartialSweep bits g t e.1)
    (gridPartialSweep_changes bits g e.1) t
  simpa only [gridPartialSweep_zero,Equiv.Perm.one_apply,gridPartialSweep_last,he] using hh.symm

lemma path_completion_finite {L : Type*} [Fintype L]
    (pos : Fin (b+1) → L → GridSlot bits) (hi : ∀t, Function.Injective (pos t))
    (hc : ∀j l i, i≠j → pos j.succ l i=pos j.castSucc l i) :
    ∃g : GridChoices bits, ∀j l, gridLayer bits g j (pos j.castSucc l)=pos j.succ l := by
  let K : PathFamily bits (Fintype.card L) :=
    {position := fun t i => pos t ((Fintype.equivFin L).symm i)
     disjoint := fun t => (hi t).comp (Fintype.equivFin L).symm.injective
     changes_only_stage := fun j k i h => hc j _ i h}
  obtain ⟨g,hg⟩ := pathEvent_nonempty K
  refine ⟨g,fun j l => ?_⟩
  have hh := hg j (Fintype.equivFin L l)
  change gridLayer bits g j (pos j.castSucc ((Fintype.equivFin L).symm
    (Fintype.equivFin L l)))=pos j.succ ((Fintype.equivFin L).symm (Fintype.equivFin L l)) at hh
  simpa only [Equiv.symm_apply_apply] using hh

variable {I : Type*} [Fintype I] [DecidableEq I] (H : PathFamily bits h)

def EndpointValid (A : Finset I) (e : I → GridSlot bits × GridSlot bits) : Prop :=
  (∀t, ∀i∈A, ∀a∈A, independentPosition (e i) t=independentPosition (e a) t → i=a) ∧
  (∀t, ∀i∈A, ∀k, independentPosition (e i) t≠H.position t k)

omit [Fintype I] [DecidableEq I] in
lemma endpointValid_mono {A B : Finset I} {e : I → GridSlot bits × GridSlot bits}
    (hAB : A⊆B) (he : EndpointValid H B e) : EndpointValid H A e :=
  ⟨fun t i hi a ha => he.1 t i (hAB hi) a (hAB ha),
   fun t i hi k => he.2 t i (hAB hi) k⟩

omit [Fintype I] [DecidableEq I] in
lemma endpointValid_completion (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (he : EndpointValid H A e) :
    ∃g : GridChoices bits, pathEvent H g ∧ ∀i∈A, gridSweep bits g (e i).1=(e i).2 := by
  let pos (t : Fin (b+1)) : Fin h ⊕ A → GridSlot bits :=
    Sum.elim (H.position t) (fun i => independentPosition (e i) t)
  have hi (t) : Function.Injective (pos t) := by
    apply (H.disjoint t).sumElim
    · intro i a hh
      exact Subtype.ext (he.1 t i i.property a a.property hh)
    · intro k i hh
      exact he.2 t i i.property k hh.symm
  have hc (j : Fin b) (l : Fin h ⊕ A) (i : Fin b) (hij : i≠j) :
      pos j.succ l i=pos j.castSucc l i := by
    cases l with
    | inl k => exact H.changes_only_stage j k i hij
    | inr a => exact independentPosition_changes (e a) j i hij
  obtain ⟨g,hg⟩ := path_completion_finite pos hi hc
  refine ⟨g,fun j k => hg j (.inl k),?_⟩
  intro i hi
  apply (gridSweep_endpoint_iff g (e i)).mpr
  intro j
  exact (endpoint_gridLayer_iff g (e i) j).mp (hg j (.inr ⟨i,hi⟩))

lemma endpointValid_of_placement_event {k : ℕ} (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k))
    (g : ConditionalChoices H) (he : ∀i∈A, gridSweep bits g.val (x i).val=(y i).val) :
    EndpointValid H A (fun i => ((x i).val,(y i).val)) := by
  constructor
  · intro t i hi a ha hp
    rw [← gridPartialSweep_endpoint g.val _ (he i hi),
      ← gridPartialSweep_endpoint g.val _ (he a ha)] at hp
    exact x.injective (Subtype.ext ((gridPartialSweep bits g.val t).injective hp))
  · intro t i hi k hp
    rw [← gridPartialSweep_endpoint g.val _ (he i hi),
      ← gridPartialSweep_path H g.val g.property] at hp
    exact (x i).property ⟨k,((gridPartialSweep bits g.val t).injective hp).symm⟩

lemma endpointValid_placement_iff {k : ℕ} (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    EndpointValid H A (fun i => ((x i).val,(y i).val)) ↔
      ∃g : ConditionalChoices H, ∀i∈A, gridSweep bits g.val (x i).val=(y i).val := by
  constructor
  · intro he
    obtain ⟨g,hg,hp⟩ := endpointValid_completion H A _ he
    exact ⟨⟨g,hg⟩,hp⟩
  · rintro ⟨g,hg⟩
    exact endpointValid_of_placement_event H x y A g hg

omit [Fintype I] in
lemma endpointValid_insert (A : Finset I) (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀t k, independentPosition (e i) t≠H.position t k)
    (ha : ∀t a, a≠i → independentPosition (e a) t≠independentPosition (e i) t) :
    EndpointValid H (insert i A) e ↔ EndpointValid H A e := by
  constructor
  · exact endpointValid_mono H (Finset.subset_insert _ _)
  · rintro ⟨hp,hq⟩
    constructor
    · intro t a hA c hC hac
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hC with rfl | hC
        · rfl
        · by_contra hne
          exact ha t c (Ne.symm hne) hac.symm
      · rcases Finset.mem_insert.mp hC with rfl | hC
        · by_contra hne
          exact ha t a hne hac
        · exact hp t a hA c hC hac
    · intro t a hA k
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hh t k
      · exact hq t a hA k

end BinaryCoordinateSweeps

end

end OAI
