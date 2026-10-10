import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedTransfer

namespace OAI

/-! Exact labelled row stages with at most four computation gates per column. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaTaggedRowStage (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : List (QMAGate × Fin (width+1)) :=
  let cols := List.ofFn e
  qmaColumnTransfer l r (cols.take (qmaGateCut width e g)) ++
    [(qmaMapGate width work r g,qmaGateArrivalColumn width e g)] ++
      qmaColumnTransfer l r (cols.drop (qmaGateCut width e g))

theorem qmaTaggedRowStage_gates (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) :
    (qmaTaggedRowStage width work l r e g).map Prod.fst = qmaRowStage width work l r e g := by
  have hp : (List.ofFn e).map (fun i => (l i,r i)) = qmaRowPairs (l ∘ e) (r ∘ e) := by
    simp [qmaRowPairs,List.map_ofFn,Function.comp_def]
  simp only [qmaTaggedRowStage,List.map_append,List.map_cons,List.map_nil,
    qmaColumnTransfer_gates,List.map_take,List.map_drop,hp,qmaRowStage]

theorem qmaNodup_filter_singleton_length {α : Type*} [DecidableEq α] (xs : List α)
    (hx : xs.Nodup) (j : α) : (xs.filter (fun i => decide (i = j))).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := (List.nodup_cons.mp hx).1
    have ht := (List.nodup_cons.mp hx).2
    by_cases hij : i = j
    · subst i
      have hz : xs.filter (fun i => decide (i = j)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k hk
        have hkj : k ≠ j := by intro he; subst k; exact hi hk
        simp [hkj]
      simp [hz]
    · simpa [hij] using ih ht

theorem qmaTaggedRowStage_count (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (j : Fin (width+1)) :
    ((qmaTaggedRowStage width work l r e g).filter (fun p => decide (p.2 = j))).length ≤ 4 := by
  let cols := List.ofFn e
  have hc : (cols.filter (fun i => decide (i = j))).length ≤ 1 :=
    qmaNodup_filter_singleton_length cols (List.nodup_ofFn.mpr e.injective) j
  have hs : ((cols.take (qmaGateCut width e g)).filter (fun i => decide (i = j))).length+
      ((cols.drop (qmaGateCut width e g)).filter (fun i => decide (i = j))).length ≤ 1 := by
    rw [←List.length_append,←List.filter_append,List.take_append_drop]
    exact hc
  simp only [qmaTaggedRowStage,List.filter_append,List.length_append,qmaColumnTransfer_count]
  change 3*((cols.take (qmaGateCut width e g)).filter (fun i => decide (i = j))).length+
      ([(qmaMapGate width work r g,qmaGateArrivalColumn width e g)].filter (fun p => decide (p.2 = j))).length+
      3*((cols.drop (qmaGateCut width e g)).filter (fun i => decide (i = j))).length ≤ 4
  have hi : ([(qmaMapGate width work r g,qmaGateArrivalColumn width e g)].filter (fun p : QMAGate × Fin (width+1) =>
      decide (p.2 = j))).length ≤ 1 := by
    exact le_trans (List.length_filter_le _ _) (by simp)
  omega

end ContinuumCoulomb

end

end OAI
