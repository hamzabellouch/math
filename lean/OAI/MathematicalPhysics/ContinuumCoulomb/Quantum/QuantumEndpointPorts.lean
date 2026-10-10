import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeLanes
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedCells
import Mathlib.Data.Finset.Sort

namespace OAI

/-! The at-most-three incident edges are assigned distinct, ordered buffered ports. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

structure QMASortedPorts {κ : Type} (C : ℕ) (color : κ → Fin C) where
  slot : Fin 3 → Fin (C+3)
  increasing : StrictMono slot
  assign : κ → Fin 3
  aligned : ∀ e, slot (assign e) = (color e).castAdd 3

theorem qmaSortedPorts_exists {κ : Type} [Fintype κ] {C : ℕ} (color : κ → Fin C)
    (hc : Fintype.card κ ≤ 3) : Nonempty (QMASortedPorts C color) := by
  let f := fun e => (color e).castAdd 3
  let s := Finset.univ.image f
  have hs : s.card ≤ 3 := (Finset.card_image_le).trans (by simpa using hc)
  obtain ⟨t,hst,_,ht⟩ := Finset.exists_subsuperset_card_eq
    (show s ⊆ Finset.univ from Finset.subset_univ _) hs
    (show 3 ≤ (Finset.univ : Finset (Fin (C+3))).card by simp)
  let iso := t.orderIsoOfFin ht
  let assign := fun e => iso.symm ⟨f e,hst (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩)⟩
  refine ⟨⟨t.orderEmbOfFin ht,(t.orderEmbOfFin ht).strictMono,assign,?_⟩⟩
  intro e
  exact congrArg Subtype.val (iso.apply_symm_apply _)

def qmaPaddedPortSlot {C : ℕ} (s : Finset (Fin C)) (a : Fin 3) : Fin (C+3) :=
  if h : a.val < s.card then (s.orderEmbOfFin rfl ⟨a.val,h⟩).castAdd 3
  else ⟨C+(a.val-s.card),by have := a.isLt; omega⟩

theorem qmaPaddedPortSlot_increasing {C : ℕ} (s : Finset (Fin C)) :
    StrictMono (qmaPaddedPortSlot s) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  by_cases ha : a.val < s.card <;> by_cases hb : b.val < s.card
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_left ha,dite_eq_left hb,Fin.val_castAdd]
    exact (s.orderEmbOfFin rfl).strictMono hab'
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_left ha,dite_eq_right hb,Fin.val_castAdd]
    have hu := (s.orderEmbOfFin rfl ⟨a.val,ha⟩).isLt
    omega
  · omega
  · change (qmaPaddedPortSlot s a).val < (qmaPaddedPortSlot s b).val
    simp only [qmaPaddedPortSlot,dite_eq_right ha,dite_eq_right hb]
    omega

def qmaCanonicalSortedPorts {κ : Type} [Fintype κ] {C : ℕ} (color : κ → Fin C)
    (hc : Fintype.card κ ≤ 3) : QMASortedPorts C color := by
  let s := Finset.univ.image color
  have hs : s.card ≤ 3 := (Finset.card_image_le).trans (by simpa using hc)
  let iso := s.orderIsoOfFin rfl
  let rank := fun e => iso.symm ⟨color e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩
  let assign := fun e => (⟨(rank e).val,lt_of_lt_of_le (rank e).isLt hs⟩ : Fin 3)
  refine ⟨qmaPaddedPortSlot s,qmaPaddedPortSlot_increasing s,assign,?_⟩
  intro e
  have hi : (assign e).val < s.card := (rank e).isLt
  simp only [qmaPaddedPortSlot,dite_eq_left hi]
  apply congrArg (Fin.castAdd 3)
  exact congrArg Subtype.val (iso.apply_symm_apply _)


namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

abbrev Incident (v : Fin M.n) := {e : M.Term // M.left e = v ∨ M.right e = v}

theorem incident_card (v : Fin M.n) :
    Fintype.card (M.Incident v) = qmaGraphDegree M.left M.right v := by
  rw [Fintype.card_subtype]
  symm
  exact Finset.sum_boole _ _

theorem incident_lane_support (v : Fin M.n) (e : M.Incident v) :
    M.laneSupport e.val (qmaLanePoint (M.laneColor e.val)
      (qmaFineGridNat (M.qubitSlots.site v))) := by
  rcases e.property with h | h
  · left
    dsimp [laneSupport,qmaLaneSupport,routeLeft,routeRight]
    rw [h]
    exact ⟨rfl,min_le_left _ _,le_max_left _ _⟩
  · right
    dsimp [laneSupport,qmaLaneSupport,routeLeft,routeRight]
    rw [h]
    exact ⟨rfl,min_le_right _ _,le_max_right _ _⟩

theorem incident_color_injective (hA : 0 < A) (v : Fin M.n) :
    Function.Injective (fun e : M.Incident v => M.laneColor e.val) := by
  intro e f hef
  change M.laneColor e.val = M.laneColor f.val at hef
  by_contra h
  have hval : e.val ≠ f.val := fun hh => h (Subtype.ext hh)
  have he := M.incident_lane_support v e
  have hf := M.incident_lane_support v f
  rw [← hef] at hf
  exact Set.disjoint_left.mp (M.lane_color_disjoint hA hval hef) he hf

def endpointPorts (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) :
    QMASortedPorts (9*B) (fun e : M.Incident v => M.laneColor e.val) :=
  qmaCanonicalSortedPorts _ ((M.incident_card v).trans_le (hd v))

theorem endpointPorts_assign_injective (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (v : Fin M.n) :
    Function.Injective (M.endpointPorts hd v).assign := by
  intro e f hef
  apply M.incident_color_injective hA v
  apply Fin.ext
  have hh := congrArg Fin.val (congrArg (M.endpointPorts hd v).slot hef)
  simpa only [(M.endpointPorts hd v).aligned,Fin.val_castAdd] using hh

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
