import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListAccuracy

namespace OAI

/-! Exact lookup formulas for fresh and retained active ports in the next
literal round. They expose the indices needed to preserve port separation. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem portAt_eq_getElem (ps : List Port) (j : ℕ) (hj : j < ps.length) :
    portAt ps j=ps[j] := by
  simp only [portAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hj,Option.getD_some]

theorem nextGroup_portAt_fresh (n : ℕ) (R : ℚ) (gs : Groups) (i j : ℕ)
    (hj : j < (groupAt gs i).length/2) :
    portAt (nextGroup n R gs i) j=(n+2*(pairStart gs i+j),R) := by
  simp only [portAt,nextGroup,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_append_left (by simpa only [List.length_map,List.length_range] using hj),
    List.getElem?_eq_getElem (by simpa only [List.length_map,List.length_range] using hj)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem nextGroup_portAt_retained (n : ℕ) (R : ℚ) (gs : Groups) (i j : ℕ)
    (hj : (groupAt gs i).length/2 ≤ j) :
    portAt (nextGroup n R gs i) j=
      portAt (groupAt gs i) (2*((groupAt gs i).length/2)+(j-(groupAt gs i).length/2)) := by
  simp only [portAt,nextGroup,List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_append_right (by simpa only [List.length_map,List.length_range] using hj)]
  simp only [List.length_map,List.length_range,unpaired,List.getElem?_drop]

theorem retained_index_lt (d j : ℕ) (hj : j < d/2+d%2) (hlarge : d/2 ≤ j) :
    2*(d/2)+(j-d/2) < d := by omega

theorem fresh_index_lt (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    pairStart gs i+j < pairCount gs := pair_index_lt gs i j hi hj

end ContinuumCoulomb.QuantumForkList

end

end OAI
