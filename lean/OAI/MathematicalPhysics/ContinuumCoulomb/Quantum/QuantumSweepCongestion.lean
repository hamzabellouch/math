import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedSweep

namespace OAI

/-! The complete literal sweep has at most four gates assigned to any grid cell. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTagRow_count (rows width : ℕ) (ps : List (QMAGate × Fin (width+1)))
    (r q : Fin (rows+1)) (j : Fin (width+1)) :
    (((ps.map (fun p => (p.1,(r,p.2)))).filter
      (fun p => decide (p.2 = (q,j)))).length) =
      if r = q then (ps.filter (fun p => decide (p.2 = j))).length else 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨g,i⟩
    by_cases hr : r = q
    · subst q
      by_cases hi : i = j <;> simp [hi,ih]
    · simp [hr,ih]

theorem qmaTaggedSweepFrom_before (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (c : QMAGridCell rows width) (hc : c.1.val < start) :
    ((qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c))).length = 0 := by
  have he : (qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [decide_eq_true_eq]
    intro hpc
    have hh := qmaTaggedSweepFrom_rows rows width start gs h p hp
    rw [hpc] at hh
    omega
  rw [he]
  rfl

theorem qmaTaggedSweepFrom_count (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (c : QMAGridCell rows width) :
    ((qmaTaggedSweepFrom rows width start gs h).filter (fun p => decide (p.2 = c))).length ≤ 4 := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom]
  | cons g gs ih =>
    rcases c with ⟨q,j⟩
    rw [qmaTaggedSweepFrom,List.filter_append,List.length_append,qmaTagRow_count]
    split_ifs with hr
    · have hq : q.val = start := by rw [←hr]
      rw [qmaTaggedSweepFrom_before rows width (start+1) gs _ (q,j) (by simp [hq]),add_zero]
      exact qmaTaggedRowStage_count _ _ _ _ _ _ _
    · simpa only [zero_add] using ih (start+1) _

def qmaSparseTags (c : QMACircuit) :
    List (QMAGate × QMAGridCell (qmaNearestCircuit c).gates.length c.work) :=
  qmaTaggedSweepFrom (qmaNearestCircuit c).gates.length c.work 0
    (qmaNearestCircuit c).gates (by omega)

theorem qmaSparseTags_gates (c : QMACircuit) :
    (qmaSparseTags c).map Prod.fst = (qmaSparseCircuit c).gates :=
  qmaTaggedSweepFrom_gates _ _ _ _ _

theorem qmaSparseTags_count (c : QMACircuit)
    (p : QMAGridCell (qmaNearestCircuit c).gates.length c.work) :
    ((qmaSparseTags c).filter (fun q => decide (q.2 = p))).length ≤ 4 :=
  qmaTaggedSweepFrom_count _ _ _ _ _ _

theorem qmaSparseTags_located (c : QMACircuit) (hc : c.WellFormed)
    (p : QMAGate × QMAGridCell (qmaNearestCircuit c).gates.length c.work)
    (hp : p ∈ qmaSparseTags c) :
    QMALocatedGate (qmaNearestCircuit c).gates.length c.work p.2.1 p.2.2 p.1 :=
  qmaTaggedSweepFrom_located _ _ _ _ _ (qmaNearestCircuit_wellFormed c hc).2
    (qmaNearestCircuit_adjacent c hc) p hp

end ContinuumCoulomb

end

end OAI
