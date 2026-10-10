import OAI.Analysis.StrictMeans.QuadraticLine

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section

def canonicalMin (a b : ℝ) : Lattice → ℝ :=
  latticeHeight (fun i => ((i:ℝ)-a)^2) (fun j => ((j:ℝ)-b)^2)
def canonicalSaddle (a b : ℝ) : Lattice → ℝ :=
  latticeHeight (fun i => ((i:ℝ)-a)^2) (fun j => -((j:ℝ)-b)^2)

def minVertex (a b : ℝ) : Lattice := toLex (⌈a-1/2⌉,⌈b-1/2⌉)
def saddleVertex (a b : ℝ) : Lattice := toLex (⌈a-1/2⌉,⌊b+1/2⌋)

lemma canonicalMin_index (a b : ℝ) (v : Lattice) :
    heightIndex (canonicalMin a b) ex ey v = if v=minVertex a b then 1 else 0 := by
  rw [canonicalMin,latticeHeight_index]
  change lineIndex (fun i => ((i:ℝ)-a)^2) (ofLex v).1 *
    lineIndex (fun j => ((j:ℝ)-b)^2) (ofLex v).2 = _
  rw [convex_line_index,convex_line_index]
  have hv : v=minVertex a b ↔ (ofLex v).1=⌈a-1/2⌉ ∧ (ofLex v).2=⌈b-1/2⌉ := by
    change v=toLex _ ↔ _
    rw [← ofLex_inj]
    exact Prod.ext_iff
  simp only [hv]
  split_ifs <;> simp_all

lemma canonicalSaddle_index (a b : ℝ) (v : Lattice) :
    heightIndex (canonicalSaddle a b) ex ey v = if v=saddleVertex a b then -1 else 0 := by
  rw [canonicalSaddle,latticeHeight_index]
  change lineIndex (fun i => ((i:ℝ)-a)^2) (ofLex v).1 *
    lineIndex (fun j => -((j:ℝ)-b)^2) (ofLex v).2 = _
  rw [convex_line_index,concave_line_index]
  have hv : v=saddleVertex a b ↔ (ofLex v).1=⌈a-1/2⌉ ∧ (ofLex v).2=⌊b+1/2⌋ := by
    change v=toLex _ ↔ _
    rw [← ofLex_inj]
    exact Prod.ext_iff
  simp only [hv]
  split_ifs <;> simp_all

lemma canonicalMin_sum (a b : ℝ) {S : Finset Lattice} (h : minVertex a b∈S) :
    ∑ v ∈ S, heightIndex (canonicalMin a b) ex ey v = 1 := by
  simp only [canonicalMin_index]
  simp [h]

lemma canonicalSaddle_sum (a b : ℝ) {S : Finset Lattice} (h : saddleVertex a b∈S) :
    ∑ v ∈ S, heightIndex (canonicalSaddle a b) ex ey v = -1 := by
  simp only [canonicalSaddle_index]
  simp [h]

end
end StrictInverseFirstPower.Grid

end

end OAI
