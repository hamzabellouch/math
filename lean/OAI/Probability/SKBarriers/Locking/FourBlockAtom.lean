import Mathlib
import OAI.Probability.SKBarriers.Locking.FourBlockTent
import OAI.Probability.SKBarriers.Locking.TentAtomMass

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem fourBlockTent_atom_le (κ : ℝ) (b l j k : List (ℝ × ℝ))
    (hl : 0<l.length) (hj : 0<j.length) {a d : ℝ}
    (hlo : ∀ p∈l,a≤p.1) (hhi : ∀ p∈j,p.1≤d) :
    scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
      (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)≤d-a := by
  have hls : fourBlockLeft κ b l j k<fourBlockRight κ b l j k := by
    change b.length<b.length+l.length+j.length
    omega
  rw [scalarTentAtomMass_eq _ _ _ _ hls]
  have HI := hhi (j.get ⟨j.length-1,by omega⟩) (List.get_mem ..)
  have HL := hlo (l.get ⟨0,hl⟩) (List.get_mem ..)
  have he1 : ((fourBlockTent κ b l j k).get
      ⟨(fourBlockRight κ b l j k).val-1,by have := (fourBlockRight κ b l j k).isLt; omega⟩).1=
      (j.get ⟨j.length-1,by omega⟩).1 := by
    simp only [List.get_eq_getElem,fourBlockTent,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map]
    simp (disch := omega) only [dite_eq_right,dite_eq_left,List.getElem_map]
    congr 2
    omega
  have he2 : ((fourBlockTent κ b l j k).get
      ⟨(fourBlockLeft κ b l j k).val,by change b.length<(fourBlockTent κ b l j k).length; rw [fourBlockTent_length]; omega⟩).1=
      (l.get ⟨0,hl⟩).1 := by
    simp only [List.get_eq_getElem,fourBlockTent,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map]
    simp (disch := omega) only [dite_eq_right,dite_eq_left,List.getElem_map,Nat.sub_self]
  rw [he1,he2]
  linarith

end SK.Analytic

end
end

end OAI
