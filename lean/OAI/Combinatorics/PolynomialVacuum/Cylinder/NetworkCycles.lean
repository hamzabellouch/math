import OAI.Combinatorics.PolynomialVacuum.Cylinder.Contour
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Support

namespace OAI

namespace PolynomialVacuumCylinder
open Classical

 

structure ClosedNetwork (M : ℕ) where
  sites : Finset (Vertex M)
  enter : sites → Fin 3
  exit : sites → Fin 3
  distinct : ∀ v,enter v≠exit v
  next : Equiv.Perm sites
  incident : ∀ v,neighbor v.val (exit v)=(next v).val
  matching : ∀ v,enter (next v)=exit v

namespace ClosedNetwork
variable {M : ℕ} (C : ClosedNetwork M)

def germ (v : C.sites) : Germ M := (v.val,C.enter v)

private theorem exists_turn (i o : Fin 3) (h : i≠o) :
    ∃ b : Bool,i+(if b then 2 else 1)=o := by
  fin_cases i <;> fin_cases o
  all_goals first | exact (h rfl).elim | decide

noncomputable def turn (v : C.sites) : Bool := (exists_turn (C.enter v) (C.exit v) (C.distinct v)).choose

theorem outgoing_turn (v : C.sites) : outgoingSlot (C.germ v) (C.turn v)=C.exit v :=
  (exists_turn (C.enter v) (C.exit v) (C.distinct v)).choose_spec

@[simp] theorem advance_turn (v : C.sites) : advance (C.germ v) (C.turn v)=C.germ (C.next v) := by
  change (neighbor v.val (outgoingSlot (C.germ v) (C.turn v)),
    outgoingSlot (C.germ v) (C.turn v)) = ((C.next v).val,C.enter (C.next v))
  rw [C.outgoing_turn,C.incident,C.matching]

noncomputable def word : ℕ → C.sites → List Bool
  | 0,_ => []
  | k+1,v => C.turn v::word k (C.next v)

@[simp] theorem word_length (k : ℕ) (v : C.sites) : (C.word k v).length=k := by
  induction k generalizing v <;> simp [word, *]

@[simp] theorem terminal_word (k : ℕ) (v : C.sites) :
    terminalGerm (C.germ v) (C.word k v)=C.germ (C.next^[k] v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [word,terminalGerm,ih,Function.iterate_succ_apply]

@[simp] theorem traced_word (k : ℕ) (v : C.sites) :
    traced (C.germ v) (C.word k v)=
      (List.range k).map (fun j => (C.next^[j] v).val) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [word,traced,C.advance_turn,ih,List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1

noncomputable def period (v : C.sites) : ℕ := Function.minimalPeriod C.next v

theorem period_pos (v : C.sites) : 0<C.period v :=
  Function.minimalPeriod_pos_of_mem_periodicPts (C.next.injective.mem_periodicPts v)

theorem orbit_terminal (v : C.sites) :
    terminalGerm (C.germ v) (C.word (C.period v) v)=C.germ v := by
  rw [C.terminal_word]
  exact congrArg C.germ Function.iterate_minimalPeriod

theorem orbit_nodup (v : C.sites) :
    (traced (C.germ v) (C.word (C.period v) v)).Nodup := by
  rw [C.traced_word]
  apply List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj he
  have he' : C.next^[i] v=C.next^[j] v := Subtype.ext he
  exact Function.iterate_injOn_Iio_minimalPeriod (List.mem_range.mp hi) (List.mem_range.mp hj) he'

noncomputable def polygon (v : C.sites) : Polygon M :=
  ⟨tracedEdges (C.germ v) (C.word (C.period v) v),
    C.germ v,C.word (C.period v) v,
    by intro he; have hl:=congrArg List.length he;
       have hz : C.period v=0 := by simpa using hl
       exact (C.period_pos v).ne' hz,
    C.orbit_nodup v,C.orbit_terminal v,rfl⟩

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI
