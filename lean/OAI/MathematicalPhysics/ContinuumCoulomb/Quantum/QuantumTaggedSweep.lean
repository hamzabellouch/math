import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedSupport

namespace OAI

/-! The literal sparse sweep comes with row and column labels. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev QMAGridCell (rows width : ℕ) := Fin (rows+1) × Fin (width+1)

def qmaTaggedSweepFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows →
      List (QMAGate × QMAGridCell rows width)
  | _,[],_ => []
  | start,g::gs,h =>
      (qmaTaggedRowStage width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start,by simp only [List.length_cons] at h; omega⟩)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩)
        (qmaSweepOrder width (rows-1-start)) g).map
          (fun p => (p.1,(⟨start,by simp only [List.length_cons] at h; omega⟩,p.2))) ++
      qmaTaggedSweepFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

theorem qmaTaggedSweepFrom_gates (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).map Prod.fst =
      qmaSweepCircuitFrom rows width start gs h := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.map_append,List.map_map,Function.comp_def,
      qmaTaggedRowStage_gates,ih,qmaSweepCircuitFrom]

theorem qmaTaggedSweepFrom_rows (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (p : QMAGate × QMAGridCell rows width)
    (hp : p ∈ qmaTaggedSweepFrom rows width start gs h) :
    start ≤ p.2.1.val ∧ p.2.1.val < start+gs.length := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom] at hp
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q,_,hq⟩ := List.mem_map.mp hp
      subst p
      simp only [List.length_cons]
      exact ⟨le_rfl,by omega⟩
    · have hh := ih (start+1) _ hp
      simp only [List.length_cons]
      omega

theorem qmaTaggedSweepFrom_located (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows)
    (hg : ∀ g ∈ gs, g.WellFormed (width+1)) (ha : ∀ g ∈ gs, g.Adjacent)
    (p : QMAGate × QMAGridCell rows width)
    (hp : p ∈ qmaTaggedSweepFrom rows width start gs h) :
    QMALocatedGate rows width p.2.1 p.2.2 p.1 := by
  induction gs generalizing start with
  | nil => simp [qmaTaggedSweepFrom] at hp
  | cons g gs ih =>
    simp only [qmaTaggedSweepFrom,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
      subst p
      exact qmaTaggedRowStage_located rows width ⟨start,by simp at h; omega⟩ _ g
        (hg g (by simp)) (ha g (by simp)) q.1 q.2 hq
    · exact ih (start+1) _ (fun g hh => hg g (by simp [hh]))
        (fun g hh => ha g (by simp [hh])) hp

end ContinuumCoulomb

end

end OAI
