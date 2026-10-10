import OAI.Analysis.Triangular.Signs.SineBarrierBase

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def localCenter (u : Fin 30) : ℤ := residue ⟨u.val/2,by omega⟩
def localNeighbor : Fin 30 → ℤ := ![-5,1,0,3,1,4,3,7,4,9,7,12,9,13,12,16,13,19,16,21,19,25,21,27,25,28,27,31,28,36]
def localPivot (u : Fin 30) : Fin 15 := ⟨u.val/2,by omega⟩
def localHalf (u : Fin 30) : ℚ := ((localNeighbor u:ℚ)-localCenter u)/2
def localPhase (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)%36
def localShift (u : Fin 30) (j : Fin 15) : ℤ := (localCenter u-residue j)/36
def cellLo (u : Fin 30) (k : Fin 100) : ℚ := min (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellHi (u : Fin 30) (k : Fin 100) : ℚ := max (localHalf u*k.val/100) (localHalf u*(k.val+1)/100)
def cellMagnitude (u : Fin 30) (k : Fin 100) : ℚ := max |cellLo u k| |cellHi u k|
def cellSeparation (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  min ((localPhase u j:ℚ)+cellLo u k) (36-((localPhase u j:ℚ)+cellHi u k))
def cellFactor (u : Fin 30) (k : Fin 100) (j : Fin 15) : ℚ :=
  if j=localPivot u then vanishingLower (cellMagnitude u k) else sineLower (cellSeparation u k j)
def cellBarrier (u : Fin 30) : ℚ := if 16≤u.val ∧ u.val≤21 then 3 else 27/500
lemma local_geometry (u : Fin 30) :
    |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j := by
  exact (show ∀ u : Fin 30, |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j by decide +kernel) u
end AtomicTriangular.Construction
end

end OAI
