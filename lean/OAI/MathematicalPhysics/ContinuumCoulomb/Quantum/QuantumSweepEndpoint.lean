import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumClockCells

namespace OAI

/-! The last clock cell lies beside the measured output on the final sweep row. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedSweepFrom_last (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate)
    (h : start+(g::gs).length ≤ rows) :
    (qmaTaggedSweepFrom rows width start (g::gs) h).getLast?.map Prod.snd =
      some ((⟨start+gs.length,by simp only [List.length_cons] at h; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-1-start-gs.length) (Fin.last width)) := by
  induction gs generalizing start g with
  | nil =>
    have hs : start < rows := by simp only [List.length_cons,List.length_nil] at h; omega
    change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
      []).getLast?.map Prod.snd = _
    simp only [List.append_nil]
    exact qmaGridStageTags_last rows width ⟨start,hs⟩ _ g
  | cons g' gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
      qmaTaggedSweepFrom rows width (start+1) (g'::gs) _).getLast?.map Prod.snd = _
    have ht : start+1+(g'::gs).length ≤ rows := by
      simp only [List.length_cons] at h ⊢; omega
    have hlast := ih (start+1) g' ht
    have hne : (qmaTaggedSweepFrom rows width (start+1) (g'::gs) ht).getLast? ≠ none := by
      intro he
      rw [he] at hlast
      simp at hlast
    rw [List.getLast?_append,Option.or_eq_left_of_isSome (Option.isSome_iff_ne_none.mpr hne)]
    have he : rows-1-(start+1)-gs.length = rows-1-start-(gs.length+1) := by omega
    rw [hlast]
    simp only [List.length_cons]
    rw [he]
    congr 2
    apply Fin.ext
    dsimp only
    omega

theorem qmaTaggedSweepFrom_last_nonempty (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hne : gs ≠ []) :
    (qmaTaggedSweepFrom rows width start gs h).getLast?.map Prod.snd =
      some ((⟨start+gs.length-1,by have := List.length_pos_iff.mpr hne; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-start-gs.length) (Fin.last width)) := by
  cases gs with
  | nil => exact (hne rfl).elim
  | cons g gs =>
    have hr : start+(g::gs).length-1 = start+gs.length := by
      simp only [List.length_cons]; omega
    have he : rows-start-(g::gs).length = rows-1-start-gs.length := by
      simp only [List.length_cons]; omega
    simpa only [hr,he] using qmaTaggedSweepFrom_last rows width start g gs h

end ContinuumCoulomb

end

end OAI
