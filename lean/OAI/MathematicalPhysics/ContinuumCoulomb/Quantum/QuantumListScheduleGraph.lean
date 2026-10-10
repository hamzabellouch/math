import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSchedule

namespace OAI

/-! The actual edge-indexed schedule represented by a literal bond/work tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorListProgram
open scoped Classical

def graph (s : State) (hs : Valid s) : QMARationalExchangeGraph where
  n := s.1
  Edge := Fin s.2.2.length
  left i := ⟨(s.2.2.get i).2.1,
    (hs.1 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩)).1⟩
  right i := ⟨(s.2.2.get i).2.2.1,
    (hs.1 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩)).2⟩
  weight i := (s.2.2.get i).2.2.2
  constant := s.2.1
  distinct i h := hs.2 _ (List.mem_map.mpr ⟨_,List.get_mem _ i,rfl⟩) (congrArg Fin.val h)

def schedule (s : State) (hs : Valid s) : QMAPathSchedule where
  graph := graph s hs
  work i := (s.2.2.get i).1

theorem graph_packed (s : State) (hs : Valid s) :
    QuantumListGraph.packed (graph s hs) (Equiv.refl _) = erase s.2.2 := by
  change List.ofFn (fun i => (s.2.2.get i).2) = s.2.2.map Prod.snd
  simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map s.2.2 Prod.snd

theorem graph_energy (s : State) (hs : Valid s) : (graph s hs).energy = energy s := by
  have h := QuantumListGraph.packed_matrix (graph s hs) (Equiv.refl _)
  rw [graph_packed] at h
  exact congrArg (sourceMatrixBottom s.1) h.symm

theorem schedule_active (s : State) (hs : Valid s) (i : (schedule s hs).graph.Edge) :
    i ∈ (schedule s hs).active ↔ 0<(s.2.2.get i).1 :=
  QMAPathSchedule.mem_active (schedule s hs) i

def indices (b : Bool) (xs : List Entry) : List (Fin xs.length) :=
  (List.finRange xs.length).filter (fun i => selected b (xs.get i))

theorem indices_nodup (b : Bool) (xs : List Entry) : (indices b xs).Nodup :=
  (List.nodup_finRange _).filter _

theorem indices_map (b : Bool) (xs : List Entry) :
    (indices b xs).map xs.get = partition b xs := by
  unfold indices partition
  have h : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map,List.ofFn_get]
  calc
    _ = ((List.finRange xs.length).map xs.get).filter (selected b) := List.filter_map.symm
    _ = _ := congrArg (List.filter (selected b)) h

theorem mem_indices (b : Bool) (xs : List Entry) (i : Fin xs.length) :
    i ∈ indices b xs ↔ selected b (xs.get i) = true := by
  simp only [indices,List.mem_filter,List.mem_finRange,true_and]

theorem indices_length (b : Bool) (xs : List Entry) :
    (indices b xs).length=(partition b xs).length := by
  have h := congrArg List.length (indices_map b xs)
  simpa only [List.length_map] using h

def indexEquiv (b : Bool) (xs : List Entry) :
    Fin (partition b xs).length ≃ {i : Fin xs.length // selected b (xs.get i)=true} :=
  (finCongr (indices_length b xs).symm).trans
    (((indices_nodup b xs).getEquiv (indices b xs)).trans
      (Equiv.subtypeEquivRight (mem_indices b xs)))

theorem indexEquiv_get (b : Bool) (xs : List Entry) (i : Fin (partition b xs).length) :
    xs.get (indexEquiv b xs i).val=(partition b xs).get i := by
  change xs.get ((indices b xs).get (Fin.cast (indices_length b xs).symm i)) = _
  have hil : i.val<(indices b xs).length := by rw [indices_length]; exact i.isLt
  have h := congrArg (fun ys : List Entry => ys[i.val]?) (indices_map b xs)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hil,List.getElem?_eq_getElem i.isLt,
    Option.map_some,Option.some.injEq,List.get_eq_getElem,Fin.val_cast] using h

theorem selected_true_iff (e : Entry) : selected true e=true ↔ 0<e.1 := by
  by_cases h : e.1=0
  · simp [selected,h]
  · simp [selected,h]
    omega

theorem selected_false_iff (e : Entry) : selected false e=true ↔ e.1=0 := by
  by_cases h : e.1=0 <;> simp [selected,h]

def activeEquiv (s : State) (hs : Valid s) :
    Fin (partition true s.2.2).length ≃ {i : (graph s hs).Edge // i ∈ (schedule s hs).active} :=
  (indexEquiv true s.2.2).trans (Equiv.subtypeEquivRight (fun i =>
    (selected_true_iff (s.2.2.get i)).trans (schedule_active s hs i).symm))

def retainedEquiv (s : State) (hs : Valid s) :
    Fin (partition false s.2.2).length ≃ {i : (graph s hs).Edge // i ∉ (schedule s hs).active} :=
  (indexEquiv false s.2.2).trans (Equiv.subtypeEquivRight (fun i => by
    apply (selected_false_iff (s.2.2.get i)).trans
    have hn : (s.2.2.get i).1=0 ↔ ¬0<(s.2.2.get i).1 := by omega
    exact hn.trans (not_congr (schedule_active s hs i)).symm))

def activePermutation (s : State) (hs : Valid s) :
    Fin (partition true s.2.2).length ≃ Fin (schedule s hs).active.card :=
  (activeEquiv s hs).trans (schedule s hs).active.equivFin

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
