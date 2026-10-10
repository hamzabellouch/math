import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridFrame

namespace OAI

/-! A concrete circuit that transfers its full active register to a fresh row per gate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaGridCircuitFrom (rows width : ℕ) :
    (start : ℕ) → (gs : List QMAGate) → start+gs.length ≤ rows → List QMAGate
  | _,[],_ => []
  | start,g::gs,h =>
      qmaGridTransfer rows width ⟨start,by simp only [List.length_cons] at h; omega⟩ ++
      [qmaMapGate width (qmaGridWork rows width)
        (qmaGridQubit rows width ⟨start+1,by simp only [List.length_cons] at h; omega⟩) g] ++
      qmaGridCircuitFrom rows width (start+1) gs (by simp only [List.length_cons] at h; omega)

theorem qmaGridCircuitFrom_length (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaGridCircuitFrom rows width start gs h).length = (3*(width+1)+1)*gs.length := by
  induction gs generalizing start with
  | nil => simp [qmaGridCircuitFrom]
  | cons g gs ih =>
    simp only [qmaGridCircuitFrom,List.length_append,List.length_cons,List.length_nil,
      qmaGridTransfer_length,ih]
    ring

theorem qmaGridTransfer_frame (rows width start : ℕ) (h : start < rows) :
    qmaGateProduct (qmaGridWork rows width) (qmaGridTransfer rows width ⟨start,h⟩)*
      qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width start (Nat.le_of_lt h))) =
    qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+1) h)) := by
  unfold qmaGridTransfer
  rw [qmaRowTransfer_matrix _ _
    (qmaGridRows_disjoint rows width _ _ (qmaGridRow_ne rows ⟨start,h⟩))]
  exact qmaWireBasis_product _ _

theorem qmaGridCircuitFrom_matrix (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    qmaGateProduct (qmaGridWork rows width) (qmaGridCircuitFrom rows width start gs h)*
      qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width start (by omega))) =
    qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+gs.length) h))*
      qmaGateProduct (qmaGridWork rows width)
        (gs.map (qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width 0))) := by
  induction gs generalizing start with
  | nil => simp [qmaGridCircuitFrom,qmaGateProduct_nil]
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    let work := qmaGridWork rows width
    let G := qmaGateMatrix work (qmaMapGate width work (qmaGridQubit rows width 0) g)
    let P := qmaWirePermutation (qmaWireBasis (qmaGridFrame rows width (start+1) hs))
    have hg : qmaGateMatrix work (qmaMapGate width work
        (qmaGridQubit rows width ⟨start+1,by omega⟩) g)*P = P*G := by
      rw [←qmaGridFrame_gate rows width (start+1) hs g]
      exact (qmaGate_wire_intertwines work _ _).symm
    simp only [qmaGridCircuitFrom,List.map_cons]
    rw [show qmaMapGate width work (qmaGridQubit rows width 0) g ::
        gs.map (qmaMapGate width work (qmaGridQubit rows width 0)) =
      [qmaMapGate width work (qmaGridQubit rows width 0) g] ++
        gs.map (qmaMapGate width work (qmaGridQubit rows width 0)) from rfl]
    simp only [qmaGateProduct_append,qmaGateProduct_singleton]
    calc
      _ = qmaGateProduct work (qmaGridCircuitFrom rows width (start+1) gs ht)*
          (qmaGateMatrix work (qmaMapGate width work
            (qmaGridQubit rows width ⟨start+1,by omega⟩) g)*P) := by
          dsimp only [P,work]
          rw [mul_assoc,mul_assoc,qmaGridTransfer_frame rows width start hs]
      _ = qmaGateProduct work (qmaGridCircuitFrom rows width (start+1) gs ht)*P*G := by
          rw [hg,mul_assoc]
      _ = _ := by
          rw [ih (start+1) ht]
          have he : start+1+gs.length = start+(g::gs).length := by simp; omega
          simp only [he,mul_assoc,G,work]

theorem qmaGridCircuitFrom_wellFormed (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hg : ∀ g ∈ gs, g.WellFormed (width+1)) :
    ∀ g ∈ qmaGridCircuitFrom rows width start gs h,
      g.WellFormed (qmaGridWork rows width+1) := by
  induction gs generalizing start with
  | nil => simp [qmaGridCircuitFrom]
  | cons g gs ih =>
    intro k hk
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    simp only [qmaGridCircuitFrom,List.mem_append,List.mem_singleton] at hk
    rcases hk with (hk | rfl) | hk
    · exact qmaGridTransfer_wellFormed rows width _ k hk
    · exact qmaMapGate_wellFormed width _ _ (qmaGridRow_injective rows width _)
        g (hg g (by simp))
    · exact ih (start+1) ht (fun k hk => hg k (by simp [hk])) k hk

end ContinuumCoulomb

end

end OAI
