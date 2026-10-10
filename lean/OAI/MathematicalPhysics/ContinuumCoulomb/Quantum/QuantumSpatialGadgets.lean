import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialThird

namespace OAI

/-! The fixed six-to-two gadget chain preserves bounded density on the same grid. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMASpatialModel.relaxDensity {d A B A' B' : ℕ} (M : QMASpatialModel d A B)
    (hA : A ≤ A') (hB : B ≤ B') : QMASpatialModel d A' B' where
  toQMARealLocalModel := M.toQMARealLocalModel
  rows := M.rows
  width := M.width
  cell := M.cell
  anchor := M.anchor
  geometry := M.geometry
  qubitDensity p := (M.qubitDensity p).trans hA
  termDensity p := (M.termDensity p).trans hB

theorem QMASpatialModel.six_to_two {A B : ℕ} (M : QMASpatialModel 6 A B)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialModel 2 (A+1077940224*B) (7516192768*B),
      |G.toQMARealLocalModel.energy-M.toQMARealLocalModel.energy| ≤ 1/N ∧
      G.rows = M.rows ∧ G.width = M.width := by
  have h3N : 1 ≤ 3*N := by linarith
  obtain ⟨M4,h4,hr4,hw4⟩ := M.subdivision (d := 3) h3N
  obtain ⟨M3,h3,hr3,hw3⟩ := M4.subdivision (d := 2) h3N
  obtain ⟨M2,h2,hr2,hw2⟩ := M3.third h3N
  have hA : (A+4^6*B)+4^4*(4*4^6*B)+4^3*(4*4^4*(4*4^6*B)) ≤ A+1077940224*B := by
    norm_num only [show (4:ℕ)^6 = 4096 by norm_num,show (4:ℕ)^4 = 256 by norm_num,
      show (4:ℕ)^3 = 64 by norm_num]
    omega
  have hB : 7*4^3*(4*4^4*(4*4^6*B)) ≤ 7516192768*B := by
    norm_num only [show (4:ℕ)^6 = 4096 by norm_num,show (4:ℕ)^4 = 256 by norm_num,
      show (4:ℕ)^3 = 64 by norm_num]
    omega
  refine ⟨M2.relaxDensity hA hB,?_,hr2.trans (hr3.trans hr4),hw2.trans (hw3.trans hw4)⟩
  change |M2.toQMARealLocalModel.energy-M.toQMARealLocalModel.energy| ≤ 1/N
  have ht := (abs_sub_le M2.toQMARealLocalModel.energy M3.toQMARealLocalModel.energy
    M.toQMARealLocalModel.energy).trans (add_le_add le_rfl
      (abs_sub_le M3.toQMARealLocalModel.energy M4.toQMARealLocalModel.energy
        M.toQMARealLocalModel.energy))
  have hN0 : N ≠ 0 := by linarith
  have he : 1/(3*N)+1/(3*N)+1/(3*N) = 1/N := by field_simp; ring
  linarith

end ContinuumCoulomb

end

end OAI
